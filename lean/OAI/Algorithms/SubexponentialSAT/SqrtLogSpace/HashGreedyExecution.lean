import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyCNF
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassBounds
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassStaged
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassSpace

/-! The actual candidate attempt is the fixed normalizer, all-clause mass
collector, and paid fixed-width padding. The only remaining query execution
premise is the concrete per-mark evaluator, including its exact caller frame. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram
open HashGreedyProgram HashGreedyProgram.NativeRound HashMassAdapter

/-- Mathematical readback of the actual unary reference records. -/
noncomputable def referenceCount {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (rows : List (List Bool)) (bits : List Bool) : ℕ :=
  match Encoding.readNat bits with
  | some (index, []) => if h : index < m then
      markedCount (HashGreedyCNF.rowAccept clauses) rows
        (fun e x => !(clauses e).eval x) ⟨index,h⟩ else 0
  | _ => 0

@[simp] theorem referenceCount_encode {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (rows : List (List Bool)) (e : Fin m) :
    referenceCount clauses rows (Encoding.encodeNat e.val) =
      markedCount (HashGreedyCNF.rowAccept clauses) rows
        (fun e x => !(clauses e).eval x) e := by
  simp [referenceCount, e.isLt]

theorem reference_sum {n m : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (rows : List (List Bool)) :
    ((RowSelectionProgram.Index.alphabet m).map (referenceCount clauses rows)).sum =
      HashSelect.mass (HashGreedyCNF.rowAccept clauses) (HashInput.violationWeight clauses) rows := by
  rw [alphabet_sum_marked (HashGreedyCNF.rowAccept clauses) rows
    (fun e x => !(clauses e).eval x) _ (referenceCount_encode clauses rows)]
  congr 1
  funext x
  exact cnf_weight clauses x

def trialState (a : State 40 896) (m depth : ℕ) (word : List Bool) : State 40 896 :=
  ⟨a.regs, Function.update a.stacks 768 (HashCandidates.normalize m depth word.reverse)⟩

def attemptBudget (a : State 40 896) (n m depth : ℕ) (queryCost : List Bool → ℕ) : ℕ :=
  HashCandidateProgram.Leaf.budget m depth +
    (massBudget a queryCost (fun _ => n + 1) m + (23 * HashSelect.loopCap n m + 20))

/-- Every marked clause is evaluated and added before comparison. The exact
full natural score is then padded; no Boolean or low-bit readout occurs. -/
theorem attempt_eval {n m depth : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (rows : List (List Bool)) (query : Cmd 40 896)
    (queryCost : List Bool → ℕ) (a : State 40 896) (word : List Bool)
    (hword : word.length = HashCandidates.payloadWidth m depth)
    (hcounter : a.stacks 778 = Encoding.encodeList id [word])
    (hclean : ∀ j : Fin 11, j ≠ 2 → j ≠ 3 → j ≠ 9 →
      a.stacks (HashCandidateProgram.Leaf.loaderStacks j) = [])
    (hlow : ∀ j : Fin 896, j.val < 12 → a.stacks j = [])
    (ht : a.stacks 767 = [])
    (hwidth : (a.stacks 780).length = HashCandidates.digitWidth m)
    (hvalue : BinaryArithmetic.toNat (a.stacks 780) = 3 * m)
    (hmword : CounterPrograms.value (a.stacks 782) = m)
    (hshape : (a.stacks 818).length = HashSelect.loopCap n m)
    (hcollector : ∀ i : Fin 896, 320 ≤ i.val → i.val ≤ 324 → a.stacks i = [])
    (hq : ∀ (e : Fin m) tail (base : State 40 896),
      Ready (fun words => words = workspace (trialState a m depth word)) base →
      ∃ t middle, t ≤ queryCost (Encoding.encodeNat e.val) ∧
        workspace middle = workspace (trialState a m depth word) ∧
        read middle = read base ∧
        BinaryArithmetic.toNat (middle.stacks 323) = markedCount
          (HashGreedyCNF.rowAccept clauses) (HashCandidates.normalize m depth word.reverse :: rows)
          (fun e x => !(clauses e).eval x) e ∧
        (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
        Eval query t
          (state recordPorts base false true false tail (Encoding.encodeNat e.val).reverse)
          (state recordPorts middle false true false tail [])) :
    ∃ t ≤ attemptBudget a n m depth queryCost, ∃ b,
      Eval (attempt (mass query)) t a b ∧
      b.stacks = Function.update (Function.update a.stacks 768
        (HashGreedyCNF.entry clauses depth rows (CounterPrograms.value word)).payload) 769
        (HashGreedyCNF.entry clauses depth rows (CounterPrograms.value word)).score := by
  let trialRows := HashCandidates.normalize m depth word.reverse :: rows
  obtain ⟨np, hnp, b, hp, hprep⟩ := HashCandidateProgram.Leaf.prepare_eval hm a word
    hword hcounter hclean hlow ht hwidth hvalue
  have hws : workspace b = workspace (trialState a m depth word) := by
    funext i
    change b.stacks (workPort i) = (Function.update a.stacks 768
      (HashCandidates.normalize m depth word.reverse)) (workPort i)
    rw [hprep]
  have hb : ReferencesReady b := by
    constructor
    · simp [hprep, ht]
    · intro i hi
      have he : a.stacks i = [] := by
        rcases hi with hi | rfl
        · exact hlow i (by omega)
        · exact hcollector 320 (by decide) (by decide)
      have hne : i ≠ 768 := by
        intro h
        subst i
        rcases hi with hi | hi
        · exact (by decide : ¬ (768 : Fin 896).val < 9) hi
        · exact (by decide : (768 : Fin 896) ≠ 320) hi
      simp [hprep, hne, he]
  have hq' : ∀ bits tail (base : State 40 896),
      (∃ e : Fin m, bits = Encoding.encodeNat e.val) →
      Ready (fun words => words = workspace b) base →
      ∃ t middle, t ≤ queryCost bits ∧ workspace middle = workspace b ∧
        read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) =
          referenceCount clauses trialRows bits ∧
        (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
        Eval query t (state recordPorts base false true false tail bits.reverse)
          (state recordPorts middle false true false tail []) := by
    intro bits tail base hvalid hb
    obtain ⟨e, he⟩ := hvalid
    subst bits
    simpa only [hws, referenceCount_encode, trialRows] using hq e tail base (by simpa only [hws] using hb)
  obtain ⟨nq, hnq, c, heq, hquery⟩ := mass_eval query (referenceCount clauses trialRows)
    queryCost (fun _ => n + 1) (fun bits => ∃ e : Fin m, bits = Encoding.encodeNat e.val) b m hb
    (by simpa [hprep] using hmword)
    (by simp [hprep, hcollector 321 (by decide) (by decide)])
    (by simp [hprep, hcollector 322 (by decide) (by decide)])
    (by simp [hprep, hcollector 323 (by decide) (by decide)])
    (by simp [hprep, hcollector 324 (by decide) (by decide)])
    (fun e => ⟨e, rfl⟩) hq'
  rw [reference_sum] at hquery
  let score := DisjointReuse.binaryNat
    (HashSelect.mass (HashGreedyCNF.rowAccept clauses) (HashInput.violationWeight clauses) trialRows)
  have hlen : score.length ≤ HashSelect.loopCap n m :=
    HashGreedyCandidate.canonical_mass_length _ _ n m trialRows
      (by simp [SAT.Assignment]) (fun x => by simpa using HashInput.violationWeight_le clauses x)
  have hv : BinaryArithmetic.toNat score =
      HashSelect.mass (HashGreedyCNF.rowAccept clauses) (HashInput.violationWeight clauses) trialRows := by
    rw [← CounterPrograms.value_eq_toNat, ← DisjointReuse.CanonicalWordProgram.ofDigits_eq_value]
    exact DisjointReuse.binaryNat_decode _
  obtain ⟨d, he, hd⟩ := HashGreedyCandidate.attempt_entry_of_query
    (HashGreedyCNF.rowAccept clauses) (HashInput.violationWeight clauses) n m depth rows
    (mass query) a b c np nq word score hword hp hprep heq hquery
    (hlow 0 (by decide)) (hlow 1 (by decide)) (hlow 2 (by decide)) hshape hlen hv
  refine ⟨np + (nq + (23 * HashSelect.loopCap n m + 20)), ?_, d, he, hd⟩
  have hbudget : massBudget b queryCost (fun _ => n + 1) m =
      massBudget a queryCost (fun _ => n + 1) m := by
    simp [massBudget, LeafOuterProgram.routeCost, hprep]
  rw [hbudget] at hnq
  exact Nat.add_le_add hnp (Nat.add_le_add_right hnq _)

def stagedAttemptBudget (a : State 40 896) (n m depth : ℕ)
    (queryCost : List Bool → ℕ) (L : ℕ) : ℕ :=
  attemptBudget a n m depth queryCost + 95 * L + 103

/-- Paid trial-source staging and cleanup are included in the actual attempt;
the only query premise is the per-mark evaluator on these produced sources. -/
theorem staged_attempt_eval {n m depth : ℕ} (clauses : Fin m → SAT.Clause (Fin n))
    (hm : 0 < m) (rows : List (List Bool)) (query : Cmd 40 896)
    (queryCost : List Bool → ℕ) (a : State 40 896) (word : List Bool)
    (hword : word.length = HashCandidates.payloadWidth m depth)
    (hcounter : a.stacks 778 = Encoding.encodeList id [word])
    (hclean : ∀ j : Fin 11, j ≠ 2 → j ≠ 3 → j ≠ 9 →
      a.stacks (HashCandidateProgram.Leaf.loaderStacks j) = [])
    (hlow : ∀ j : Fin 896, j.val < 12 → a.stacks j = [])
    (ht : a.stacks 767 = [])
    (hwidth : (a.stacks 780).length = HashCandidates.digitWidth m)
    (hvalue : BinaryArithmetic.toNat (a.stacks 780) = 3 * m)
    (hmword : CounterPrograms.value (a.stacks 782) = m)
    (hshape : (a.stacks 818).length = HashSelect.loopCap n m)
    (hcollector : ∀ i : Fin 896, 320 ≤ i.val → i.val ≤ 324 → a.stacks i = [])
    (L : ℕ)
    (hsource : ∀ i ∈ ([777,782,783,784,785] : List (Fin 896)), (a.stacks i).length ≤ L)
    (hC : HashCandidates.payloadWidth m depth ≤ L)
    (hempty : ∀ i ∈ HashMassStaged.stagedPorts, a.stacks i = [])
    (hq : ∀ (e : Fin m) tail (base : State 40 896),
      Ready (fun words => words = workspace (LeafOuterNative.trialStaged (trialState a m depth word))) base →
      ∃ t middle, t ≤ queryCost (Encoding.encodeNat e.val) ∧
        workspace middle = workspace (LeafOuterNative.trialStaged (trialState a m depth word)) ∧
        read middle = read base ∧
        BinaryArithmetic.toNat (middle.stacks 323) = markedCount
          (HashGreedyCNF.rowAccept clauses) (HashCandidates.normalize m depth word.reverse :: rows)
          (fun e x => !(clauses e).eval x) e ∧
        (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
        Eval query t
          (state recordPorts base false true false tail (Encoding.encodeNat e.val).reverse)
          (state recordPorts middle false true false tail [])) :
    ∃ t ≤ stagedAttemptBudget a n m depth queryCost L, ∃ b,
      Eval (attempt (HashMassStaged.command query)) t a b ∧
      b.stacks = Function.update (Function.update a.stacks 768
        (HashGreedyCNF.entry clauses depth rows (CounterPrograms.value word)).payload) 769
        (HashGreedyCNF.entry clauses depth rows (CounterPrograms.value word)).score := by
  let trialRows := HashCandidates.normalize m depth word.reverse :: rows
  obtain ⟨np, hnp, b, hp, hprep⟩ := HashCandidateProgram.Leaf.prepare_eval hm a word
    hword hcounter hclean hlow ht hwidth hvalue
  have hws : workspace (LeafOuterNative.trialStaged b) =
      workspace (LeafOuterNative.trialStaged (trialState a m depth word)) := by
    funext i
    exact congrFun (HashMassStaged.staged_stacks_congr b (trialState a m depth word) hprep) (workPort i)
  have hb : ReferencesReady b := by
    constructor
    · simp [hprep, ht]
    · intro i hi
      have he : a.stacks i = [] := by
        rcases hi with hi | rfl
        · exact hlow i (by omega)
        · exact hcollector 320 (by decide) (by decide)
      have hne : i ≠ 768 := by
        intro h
        subst i
        rcases hi with hi | hi
        · exact (by decide : ¬ (768 : Fin 896).val < 9) hi
        · exact (by decide : (768 : Fin 896) ≠ 320) hi
      simp [hprep, hne, he]
  have hq' : ∀ bits tail (base : State 40 896),
      (∃ e : Fin m, bits = Encoding.encodeNat e.val) →
      Ready (fun words => words = workspace (LeafOuterNative.trialStaged b)) base →
      ∃ t middle, t ≤ queryCost bits ∧ workspace middle = workspace (LeafOuterNative.trialStaged b) ∧
        read middle = read base ∧ BinaryArithmetic.toNat (middle.stacks 323) =
          referenceCount clauses trialRows bits ∧
        (middle.stacks 323).length ≤ n + 1 ∧ middle.stacks 324 = [] ∧
        Eval query t (state recordPorts base false true false tail bits.reverse)
          (state recordPorts middle false true false tail []) := by
    intro bits tail base hvalid hb
    obtain ⟨e, he⟩ := hvalid
    subst bits
    simpa only [hws, referenceCount_encode, trialRows] using hq e tail base (by simpa only [hws] using hb)
  have hemptyB : ∀ i ∈ HashMassStaged.stagedPorts, b.stacks i = [] := by
    intro i hi
    have hne : i ≠ 768 := by
      simp only [HashMassStaged.stagedPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simpa [hprep,hne] using hempty i hi
  have hcB : ∀ i : Fin 896, 321 ≤ i.val → i.val ≤ 324 → b.stacks i = [] := by
    intro i hi hj
    have hne : i ≠ 768 := by intro he; subst i; omega
    simpa [hprep,hne] using hcollector i (by omega) hj
  obtain ⟨nq, hnq, c, heq, hquery⟩ := HashMassStaged.eval query (referenceCount clauses trialRows)
    queryCost (fun _ => n + 1) (fun bits => ∃ e : Fin m, bits = Encoding.encodeNat e.val) b m hb
    (by simpa [hprep] using hmword) hcB hemptyB (fun e => ⟨e, rfl⟩) hq'
  rw [reference_sum] at hquery
  let score := DisjointReuse.binaryNat
    (HashSelect.mass (HashGreedyCNF.rowAccept clauses) (HashInput.violationWeight clauses) trialRows)
  have hlen : score.length ≤ HashSelect.loopCap n m :=
    HashGreedyCandidate.canonical_mass_length _ _ n m trialRows
      (by simp [SAT.Assignment]) (fun x => by simpa using HashInput.violationWeight_le clauses x)
  have hv : BinaryArithmetic.toNat score =
      HashSelect.mass (HashGreedyCNF.rowAccept clauses) (HashInput.violationWeight clauses) trialRows := by
    rw [← CounterPrograms.value_eq_toNat, ← DisjointReuse.CanonicalWordProgram.ofDigits_eq_value]
    exact DisjointReuse.binaryNat_decode _
  obtain ⟨d, he, hd⟩ := HashGreedyCandidate.attempt_entry_of_query
    (HashGreedyCNF.rowAccept clauses) (HashInput.violationWeight clauses) n m depth rows
    (HashMassStaged.command query) a b c np nq word score hword hp hprep heq hquery
    (hlow 0 (by decide)) (hlow 1 (by decide)) (hlow 2 (by decide)) hshape hlen hv
  refine ⟨np + (nq + (23 * HashSelect.loopCap n m + 20)), ?_, d, he, hd⟩
  have hbudget : massBudget b queryCost (fun _ => n + 1) m =
      massBudget a queryCost (fun _ => n + 1) m := by
    simp [massBudget, LeafOuterProgram.routeCost, hprep]
  have hsourceB : ∀ i ∈ ([777,782,783,784,785] : List (Fin 896)), (b.stacks i).length ≤ L := by
    intro i hi
    have hne : i ≠ 768 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide
    simpa [hprep,hne] using hsource i hi
  have hcandidateB : (b.stacks 768).length ≤ L := by
    simpa [hprep] using hC
  have hstage := HashMassStaged.stagingBudget_le_sources b L hemptyB hsourceB hcandidateB
  unfold HashMassStaged.budget at hnq
  rw [hbudget] at hnq
  unfold stagedAttemptBudget attemptBudget
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashGreedyExecution
