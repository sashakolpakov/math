import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyRound
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.CountModel

/-! Exact reference values for the payload and full natural score physically
produced by the native candidate attempt. These accessors are proof objects;
the executable program retains only the current word and running minimum. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate

open BitProgram StructuredCalls SqrtLog
open HashGreedyProgram HashGreedyProgram.NativeRound

/-- The actual parser reverses the binary odometer word before canonicalizing
its indexed ternary digits. -/
def candidate (m depth rank : ℕ) : List Bool :=
  HashCandidates.normalize m depth
    (ExecCNFTupleEnumeration.fixedBits (HashCandidates.payloadWidth m depth) rank).reverse

@[simp] theorem candidate_length (m depth rank : ℕ) :
    (candidate m depth rank).length = HashCandidates.payloadWidth m depth := by
  simp [candidate]

theorem candidate_at_word {m depth : ℕ} (word : List Bool)
    (hlen : word.length = HashCandidates.payloadWidth m depth) :
    candidate m depth (CounterPrograms.value word) = HashCandidates.normalize m depth word.reverse := by
  have h := HashCandidateRank.payload_wordRank word hlen
  simpa only [HashCandidates.payload, HashCandidateRank.wordRank, candidate] using
    congrArg (HashCandidates.normalize m depth) h

/-- Canonical alphabet width never exceeds an actual word encoding 3*m. -/
theorem digitWidth_le_word_length {m : ℕ} (hm : 0 < m) (word : List Bool)
    (hvalue : CounterPrograms.value word = 3 * m) :
    HashCandidates.digitWidth m ≤ word.length := by
  have hlt : 3 * m < 2 ^ word.length := by
    simpa only [hvalue] using ExecCNFTupleOdometer.value_lt_power_length word
  have hlog := Nat.log_lt_of_lt_pow (by omega : 3 * m ≠ 0) hlt
  unfold HashCandidates.digitWidth DyadicWidth.width
  omega

theorem candidate_mem {m : ℕ} (hm : 0 < m) (depth rank : ℕ) :
    candidate m depth rank ∈ HashSelectProgram.generatedPayloads
      (HashFamilyPayload.alphabet m (HashCandidates.digitWidth m)) depth :=
  HashCandidates.normalize_mem hm depth _

theorem candidate_covers {m depth : ℕ} (h : HashFamily.Candidate m depth) :
    ∃ rank < 2 ^ HashCandidates.payloadWidth m depth,
      candidate m depth rank = HashFamilyPayload.encode (HashCandidates.digitWidth m) h := by
  obtain ⟨i, hi⟩ := HashCandidates.normalized_covers_candidate h
  exact ⟨i.val, i.isLt, hi⟩

/-- Full natural mass is encoded in the common retained score width. -/
def entry {X : Type*} [Fintype X] (rowAccept : List Bool → X → Bool) (weight : X → ℕ)
    (n m depth : ℕ) (rows : List (List Bool)) (rank : ℕ) : BinaryArgmin.Entry :=
  ⟨candidate m depth rank, ExecCNFTupleEnumeration.fixedBits (HashSelect.loopCap n m)
    (HashSelect.mass rowAccept weight (candidate m depth rank :: rows))⟩

theorem entry_fits {X : Type*} [Fintype X]
    (rowAccept : List Bool → X → Bool) (weight : X → ℕ)
    (n m depth : ℕ) (rows : List (List Bool)) (rank : ℕ) :
    BinaryArgmin.Fits (HashSelect.loopCap n m) (HashCandidates.payloadWidth m depth)
      (entry rowAccept weight n m depth rows rank) := by
  constructor <;> simp [entry]

theorem entry_value {X : Type*} [Fintype X]
    (rowAccept : List Bool → X → Bool) (weight : X → ℕ)
    (n m depth : ℕ) (rows : List (List Bool)) (rank : ℕ)
    (hx : Fintype.card X ≤ 2 ^ n) (hw : ∀ x, weight x ≤ m) :
    BinaryArgmin.value (entry rowAccept weight n m depth rows rank) =
      HashSelect.mass rowAccept weight (candidate m depth rank :: rows) := by
  rw [BinaryArgmin.value, entry, ← CounterPrograms.value_eq_toNat]
  exact ExecCNFTupleEnumeration.fixedBits_value _ _
    (HashGreedy.mass_lt_loopCap_capacity rowAccept weight _ n m hx hw)

/-- Canonical mass words fit the saved round-count shape even when all m
marked counts contribute. An n+1 count bound is not used for this score. -/
theorem canonical_mass_length {X : Type*} [Fintype X]
    (rowAccept : List Bool → X → Bool) (weight : X → ℕ)
    (n m : ℕ) (rows : List (List Bool))
    (hx : Fintype.card X ≤ 2 ^ n) (hw : ∀ x, weight x ≤ m) :
    (DisjointReuse.binaryNat (HashSelect.mass rowAccept weight rows)).length ≤
      HashSelect.loopCap n m := by
  have h := DisjointReuse.binaryNat_length_le
    (HashSelect.initial_mass_lt_cap_power rowAccept weight rows n m hx hw).le
  unfold HashSelect.loopCap
  omega

theorem padded_score_eq (word shape : List Bool) (score : ℕ)
    (hlen : word.length ≤ shape.length) (hvalue : BinaryArithmetic.toNat word = score) :
    ModularArithmetic.padTo shape word = ExecCNFTupleEnumeration.fixedBits shape.length score := by
  apply ExecCNFTupleEnumeration.word_eq_of_length_value
  · simp [ModularArithmetic.padTo_length]
  · have hv := (PadScore.exact_value word shape hlen).1
    have hscore : score < 2 ^ shape.length := by
      rw [← hvalue]
      exact (ModularArithmetic.toNat_lt_pow_length word).trans_le
        (Nat.pow_le_pow_right (by decide) hlen)
    rw [CounterPrograms.value_eq_toNat, hv, hvalue,
      ExecCNFTupleEnumeration.fixedBits_value _ _ hscore]

/-- Actual candidate preparation, exact query and paid padding produce exactly
the reference entry used in the proven native minimum. The query premise is an
actual execution and exact full frame; the complete mass adapter must supply it. -/
theorem attempt_entry_of_query {X : Type*} [Fintype X]
    (rowAccept : List Bool → X → Bool) (weight : X → ℕ)
    (n m depth : ℕ) (rows : List (List Bool)) (mass : Cmd 40 896)
    (a b c : State 40 896) (np nq : ℕ) (word score : List Bool)
    (hword : word.length = HashCandidates.payloadWidth m depth)
    (hp : Eval HashCandidateProgram.Leaf.prepare np a b)
    (hprep : b.stacks = Function.update a.stacks 768
      (HashCandidates.normalize m depth word.reverse))
    (hq : Eval mass nq b c) (hquery : c.stacks = Function.update b.stacks 769 score)
    (h0 : a.stacks 0 = []) (h1 : a.stacks 1 = []) (h2 : a.stacks 2 = [])
    (hshape : (a.stacks 818).length = HashSelect.loopCap n m)
    (hlen : score.length ≤ HashSelect.loopCap n m)
    (hvalue : BinaryArithmetic.toNat score = HashSelect.mass rowAccept weight
      (HashCandidates.normalize m depth word.reverse :: rows)) :
    ∃ d, Eval (attempt mass) (np + (nq + (23 * HashSelect.loopCap n m + 20))) a d ∧
      d.stacks = Function.update (Function.update a.stacks 768
        (entry rowAccept weight n m depth rows (CounterPrograms.value word)).payload) 769
        (entry rowAccept weight n m depth rows (CounterPrograms.value word)).score := by
  obtain ⟨d, he, hd, _, _⟩ := attempt_eval_of_query mass a b c np nq _ score hp hprep hq hquery
    h0 h1 h2 (by simpa [hshape] using hlen)
  refine ⟨d, by simpa only [hshape] using he, ?_⟩
  rw [hd, padded_score_eq score (a.stacks 818) _ (by simpa [hshape] using hlen) hvalue]
  simp only [entry, candidate_at_word word hword, hshape]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCandidate
