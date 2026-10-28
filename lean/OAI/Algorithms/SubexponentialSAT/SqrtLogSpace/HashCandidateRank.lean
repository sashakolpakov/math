import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateProgram

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateRank

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

/-- Proof-level rank of the actual retained word, including leading zeroes. -/
def wordRank {m depth : ℕ} (word : List Bool)
    (hlen : word.length = HashCandidates.payloadWidth m depth) :
    Fin (2 ^ HashCandidates.payloadWidth m depth) :=
  ⟨CounterPrograms.value word, by
    simpa only [hlen] using ExecCNFTupleOdometer.value_lt_power_length word⟩

/-- The parser reverses the current odometer word, exactly as the reference
candidate accessor does. No native decoding of the exponential rank occurs. -/
theorem payload_wordRank {m depth : ℕ} (word : List Bool)
    (hlen : word.length = HashCandidates.payloadWidth m depth) :
    HashCandidates.payload m depth (wordRank word hlen) = word.reverse := by
  apply congrArg List.reverse
  apply ExecCNFTupleEnumeration.word_eq_of_length_value
  · simp [hlen]
  · exact ExecCNFTupleEnumeration.fixedBits_value _ _ (wordRank word hlen).isLt

/-- A singleton shape contains exactly the one physical payload word. -/
theorem tuple_eq_singleton_flatten {words : List (List Bool)} {width : ℕ}
    (hshape : words.map List.length = [width]) : words = [words.flatten] := by
  obtain ⟨word, rfl, _⟩ := List.map_eq_singleton_iff.mp hshape
  simp

/-- The actual preparation command emits the reference candidate at the
current word's rank and preserves every other physical leaf stack. -/
theorem prepare_eval {m depth : ℕ} (hm : 0 < m)
    (a : StructuredProgram.State 40 896) (word : List Bool)
    (hlen : word.length = HashCandidates.payloadWidth m depth)
    (hcounter : a.stacks 778 = Encoding.encodeList id [word])
    (hclean : ∀ j : Fin 11, j ≠ 2 → j ≠ 3 → j ≠ 9 →
      a.stacks (HashCandidateProgram.Leaf.loaderStacks j) = [])
    (hlow : ∀ j : Fin 896, j.val < 12 → a.stacks j = [])
    (ht : a.stacks 767 = [])
    (hwidth : (a.stacks 780).length = HashCandidates.digitWidth m)
    (hvalue : BinaryArithmetic.toNat (a.stacks 780) = 3 * m) :
    ∃ n ≤ HashCandidateProgram.Leaf.budget m depth,
      ∃ b, Eval HashCandidateProgram.Leaf.prepare n a b ∧
        b.stacks = Function.update a.stacks 768
          (HashCandidates.normalize m depth
            (HashCandidates.payload m depth (wordRank word hlen))) := by
  simpa only [payload_wordRank] using
    HashCandidateProgram.Leaf.prepare_eval hm a word hlen hcounter hclean hlow ht hwidth hvalue

/-- Rank identification, measured execution and all-prefix source storage
refer to the same compiled preparation run. -/
theorem trace_space {m depth : ℕ} (hm : 0 < m)
    (a : StructuredProgram.State 40 896) (word : List Bool) (L : ℕ)
    (hL : ∀ j, (a.stacks j).length ≤ L)
    (hlen : word.length = HashCandidates.payloadWidth m depth)
    (hcounter : a.stacks 778 = Encoding.encodeList id [word])
    (hclean : ∀ j : Fin 11, j ≠ 2 → j ≠ 3 → j ≠ 9 →
      a.stacks (HashCandidateProgram.Leaf.loaderStacks j) = [])
    (hlow : ∀ j : Fin 896, j.val < 12 → a.stacks j = [])
    (ht : a.stacks 767 = [])
    (hwidth : (a.stacks 780).length = HashCandidates.digitWidth m)
    (hvalue : BinaryArithmetic.toNat (a.stacks 780) = 3 * m) :
    ∃ n ≤ HashCandidateProgram.Leaf.budget m depth + 1,
      ∃ b : StructuredProgram.State 40 896,
        Trace HashCandidateProgram.Leaf.program n
          (a.withPC (some HashCandidateProgram.Leaf.program.entry)) (b.withPC none) ∧
        b.stacks = Function.update a.stacks 768
          (HashCandidates.normalize m depth
            (HashCandidates.payload m depth (wordRank word hlen))) ∧
        ∀ k c, k ≤ n → Trace HashCandidateProgram.Leaf.program k
          (a.withPC (some HashCandidateProgram.Leaf.program.entry)) c →
          ∀ j, (c.stacks j).length ≤ 896 * L + HashCandidateProgram.Leaf.budget m depth + 1 := by
  simpa only [payload_wordRank] using
    HashCandidateProgram.Leaf.trace_space hm a word L hL hlen hcounter hclean hlow ht hwidth hvalue

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashCandidateRank
