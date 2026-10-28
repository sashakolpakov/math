import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadIncrementalSequential

namespace OAI.Algorithms

/-! Exact ordering interface for the existing natural-number selector. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadIncremental

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators

section Weighted
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ} [NeZero r]

def sequentialIncidenceCount (alphabet : List (Word r Q)) (pairs : List (I × I))
    (vertices : List V) (factors : List E) (default : Word r Q)
    (n : ℕ) (fixed : List (Word r Q)) : ℕ :=
  (PackingProgram.unweightedCounts ivar factor alphabet
    (pairs.map Sum.inl ++ headTerms (I := I) (Q := Q) vertices)
    (headsFirstIndices vertices factors) (List.range' fixed.length n)
    (decode default fixed)).1

omit [NeZero r] in
omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem sequentialNumerator_split (alphabet : List (Word r Q)) (pairs : List (I × I))
    (vertices : List V) (factors : List E) (w : PackingProgram.Weights)
    (default : Word r Q) (n : ℕ) (fixed : List (Word r Q)) :
    PackingProgram.sequentialNumerator ivar factor alphabet
      (pairs.map Sum.inl ++ headTerms (I := I) (Q := Q) vertices)
      (headsFirstIndices vertices factors) w default n fixed =
      w.incidence * sequentialIncidenceCount ivar factor alphabet pairs vertices factors default n fixed +
      w.head * sequentialHeadCount ivar factor alphabet pairs vertices factors default n fixed := by
  exact PackingProgram.numerator_split ivar factor alphabet _ _ w _ _

omit [Fintype I] [Fintype E] [DecidableEq I] in
theorem sequentialNumerator_order_head
    (alphabet : List (Word r Q)) (haN : alphabet.Nodup) (haC : ∀ z, z ∈ alphabet)
    (pairs : List (I × I)) (vertices : List V) (factors : List E)
    (hvN : vertices.Nodup) (hvC : ∀ v, v ∈ vertices)
    (w : PackingProgram.Weights) (default : Word r Q) (n : ℕ)
    (fixed : List (Word r Q))
    (hsize : n + 1 + fixed.length = (headsFirstIndices vertices factors).length)
    (hhead : fixed.length < vertices.length) (x y : Word r Q) :
    PackingProgram.sequentialNumerator ivar factor alphabet
      (pairs.map Sum.inl ++ headTerms (I := I) (Q := Q) vertices)
      (headsFirstIndices vertices factors) w default n (x :: fixed) ≤
    PackingProgram.sequentialNumerator ivar factor alphabet
      (pairs.map Sum.inl ++ headTerms (I := I) (Q := Q) vertices)
      (headsFirstIndices vertices factors) w default n (y :: fixed) ↔
      w.incidence * sequentialIncidenceCount ivar factor alphabet pairs vertices factors default n (x :: fixed) +
        (2 * alphabet.length^4 * w.head) * prefixOverlap x fixed ≤
      w.incidence * sequentialIncidenceCount ivar factor alphabet pairs vertices factors default n (y :: fixed) +
        (2 * alphabet.length^4 * w.head) * prefixOverlap y fixed := by
  rw [sequentialNumerator_split, sequentialNumerator_split]
  exact sequentialHead_order_iff ivar factor alphabet haN haC pairs vertices factors hvN hvC
    default n fixed hsize hhead x y w.incidence w.head _ _

omit [Fintype I] [Fintype E] [DecidableEq I] in
theorem sequentialNumerator_order_factor
    (alphabet : List (Word r Q)) (haN : alphabet.Nodup) (haC : ∀ z, z ∈ alphabet)
    (pairs : List (I × I)) (vertices : List V) (factors : List E)
    (hvN : vertices.Nodup) (hvC : ∀ v, v ∈ vertices)
    (w : PackingProgram.Weights) (default : Word r Q) (n : ℕ)
    (fixed : List (Word r Q)) (hfactor : vertices.length ≤ fixed.length)
    (x y : Word r Q) :
    PackingProgram.sequentialNumerator ivar factor alphabet
      (pairs.map Sum.inl ++ headTerms (I := I) (Q := Q) vertices)
      (headsFirstIndices vertices factors) w default n (x :: fixed) ≤
    PackingProgram.sequentialNumerator ivar factor alphabet
      (pairs.map Sum.inl ++ headTerms (I := I) (Q := Q) vertices)
      (headsFirstIndices vertices factors) w default n (y :: fixed) ↔
      w.incidence * sequentialIncidenceCount ivar factor alphabet pairs vertices factors default n (x :: fixed) ≤
      w.incidence * sequentialIncidenceCount ivar factor alphabet pairs vertices factors default n (y :: fixed) := by
  rw [sequentialNumerator_split, sequentialNumerator_split,
    sequentialHead_factor_constant ivar factor alphabet haN haC pairs vertices factors hvN hvC
      default n fixed hfactor x y]
  omega

end Weighted
end SubexponentialSAT.SqrtLog.PackingHeadIncremental

end OAI.Algorithms
