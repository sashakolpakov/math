import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadIncrementalWeighted
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadProgramPrefix

namespace OAI.Algorithms

/-! The exact score returned by the physical one-hot overlap loop, including
its heads-first phase gate, preserves the original selector ordering. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadIncremental
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators

variable {r Q : ℕ}

def physicalOverlap (headCount : ℕ) (candidate : Word r Q)
    (fixed : List (Word r Q)) : ℕ :=
  if fixed.length < headCount then
    PackingHeadProgramPrefix.score (SubexponentialSAT.Subexp.ReadPlan.encodeWord candidate)
      (fixed.reverse.map SubexponentialSAT.Subexp.ReadPlan.encodeWord)
  else 0

theorem score_encode_prefix (candidate : Word r Q) (fixed : List (Word r Q)) :
    PackingHeadProgramPrefix.score (SubexponentialSAT.Subexp.ReadPlan.encodeWord candidate)
      (fixed.reverse.map SubexponentialSAT.Subexp.ReadPlan.encodeWord) =
      prefixOverlap candidate fixed := by
  simp only [PackingHeadProgramPrefix.score, List.map_map, Function.comp_def,
    PackingHeadProgramAnd.jointTrue, encodeWord_and_count]
  simp [prefixOverlap]

theorem physicalOverlap_head (heads : ℕ) (candidate : Word r Q)
    (fixed : List (Word r Q)) (h : fixed.length < heads) :
    physicalOverlap heads candidate fixed = prefixOverlap candidate fixed := by
  simp only [physicalOverlap, ite_eq_left h, score_encode_prefix]

theorem physicalOverlap_factor (heads : ℕ) (candidate : Word r Q)
    (fixed : List (Word r Q)) (h : heads ≤ fixed.length) :
    physicalOverlap heads candidate fixed = 0 := by
  simp [physicalOverlap, Nat.not_lt.mpr h]

section Ordering
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E] [NeZero r]
variable (ivar : I → V) (factor : I → E)

omit [Fintype I] [Fintype E] [DecidableEq I] in
theorem sequentialNumerator_order_physical
    (alphabet : List (Word r Q)) (haN : alphabet.Nodup) (haC : ∀ z, z ∈ alphabet)
    (pairs : List (I × I)) (vertices : List V) (factors : List E)
    (hvN : vertices.Nodup) (hvC : ∀ v, v ∈ vertices)
    (w : PackingProgram.Weights) (default : Word r Q) (n : ℕ)
    (fixed : List (Word r Q))
    (hsize : n + 1 + fixed.length = (headsFirstIndices vertices factors).length)
    (x y : Word r Q) :
    PackingProgram.sequentialNumerator ivar factor alphabet
      (pairs.map Sum.inl ++ headTerms (I := I) (Q := Q) vertices)
      (headsFirstIndices vertices factors) w default n (x :: fixed) ≤
    PackingProgram.sequentialNumerator ivar factor alphabet
      (pairs.map Sum.inl ++ headTerms (I := I) (Q := Q) vertices)
      (headsFirstIndices vertices factors) w default n (y :: fixed) ↔
      w.incidence * sequentialIncidenceCount ivar factor alphabet pairs vertices factors default n (x :: fixed) +
        (2 * alphabet.length^4 * w.head) * physicalOverlap vertices.length x fixed ≤
      w.incidence * sequentialIncidenceCount ivar factor alphabet pairs vertices factors default n (y :: fixed) +
        (2 * alphabet.length^4 * w.head) * physicalOverlap vertices.length y fixed := by
  by_cases h : fixed.length < vertices.length
  · simpa only [physicalOverlap, ite_eq_left h, score_encode_prefix] using
      sequentialNumerator_order_head ivar factor alphabet haN haC pairs vertices factors hvN hvC
        w default n fixed hsize h x y
  · have hf : vertices.length ≤ fixed.length := Nat.le_of_not_gt h
    simpa only [physicalOverlap, ite_eq_right h, mul_zero, add_zero] using
      sequentialNumerator_order_factor ivar factor alphabet haN haC pairs vertices factors hvN hvC
        w default n fixed hf x y
end Ordering
end SubexponentialSAT.SqrtLog.PackingHeadIncremental

end OAI.Algorithms
