import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingHeadIncremental
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingPrefixScore

namespace OAI.Algorithms

/-! The finite head sum is exactly the actual numbered completion numerator. -/
namespace SubexponentialSAT.SqrtLog.PackingHeadIncremental

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.LocalExpectation SubexponentialSAT.Subexp.LocalExpectation
open SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators

private theorem completionCount_zero {A W : Type*} [DecidableEq A]
    (alphabet : List W) (remaining : List A) (ω : A → W) :
    completionCount alphabet (fun _ => 0) remaining ω = 0 := by
  induction remaining generalizing ω with
  | nil => rfl
  | cons a remaining ih => simp [completionCount, ih]

section Numbered
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ}

def headTerms (vertices : List V) : List (ScoreTerm I V Q) :=
  (List.finRange Q).flatMap (fun t =>
    (vertices.product vertices).map (fun p => Sum.inr (t, p.1, p.2)))

omit [Fintype I] [Fintype V] [Fintype E] [DecidableEq I] in
theorem numbered_head_pair (alphabet : List (Word r Q)) (indices : List (V ⊕ E))
    (remaining : List ℕ) (ω : ℕ → Word r Q) (t : Fin Q) (v u : V) :
    scaledCount alphabet
      (fun η => PackingProgram.headIndicator (Sum.inr (t,v,u) : ScoreTerm I V Q)
        (fun i => η (indexCode indices i)))
      (numberedScoreSupport ivar factor indices (Sum.inr (t,v,u))) 4 remaining ω =
    pairCount alphabet remaining t (indexCode indices (Sum.inl v))
      (indexCode indices (Sum.inl u)) ω := by
  simp [pairCount, PackingProgram.headIndicator, numberedScoreSupport, scoreSupport]

omit [Fintype I] [Fintype E] [DecidableEq I] in
theorem unweighted_head_eq (alphabet : List (Word r Q)) (pairs : List (I × I))
    (vertices : List V) (hvN : vertices.Nodup) (hvC : ∀ v, v ∈ vertices)
    (indices : List (V ⊕ E)) (remaining : List ℕ) (ω : ℕ → Word r Q) :
    (PackingProgram.unweightedCounts ivar factor alphabet
      (pairs.map Sum.inl ++ headTerms (I := I) (Q := Q) vertices)
      indices remaining ω).2 =
      headCount alphabet (fun v : V => indexCode indices (Sum.inl v)) remaining ω := by
  simp only [PackingProgram.unweightedCounts, commonNumerator, List.map_append,
    List.sum_append, List.map_map, Function.comp_def]
  have hzero : (pairs.map (fun p => scaledCount alphabet
      (fun η => PackingProgram.headIndicator (Sum.inl p : ScoreTerm I V Q)
        (fun i => η (indexCode indices i)))
      (numberedScoreSupport ivar factor indices (Sum.inl p : ScoreTerm I V Q)) 4 remaining ω)).sum = 0 := by
    simp [scaledCount, PackingProgram.headIndicator, completionCount_zero]
  rw [hzero, zero_add]
  change ((headScoreTerms vertices Q).map _).sum = _
  rw [headScoreTerms_sum vertices hvN hvC]
  simp only [numbered_head_pair ivar factor, headCount]

end Numbered
end SubexponentialSAT.SqrtLog.PackingHeadIncremental

end OAI.Algorithms
