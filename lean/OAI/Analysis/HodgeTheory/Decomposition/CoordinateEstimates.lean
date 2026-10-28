import OAI.Analysis.HodgeTheory.Decomposition.AdjointCoefficients
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricBounds

/-! # Coordinate Estimates -/

namespace OAI.Analysis.HodgeTheory.Decomposition.CoordinateEstimates.Constructions

noncomputable section

/-! Uniform comparison of the actual weighted form metric with coordinate
norms on every compact chart subset. -/

open scoped ContDiff

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricBounds.CM.Construction

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

include he

theorem projectiveWeightedFormOperator_uniform_lower
    {K : Set (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K,
      ∀ u : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n,
        c * ‖u‖ ^ 2 ≤ inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z u) u := by
  let B := fun z => (innerSL ℝ).comp (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z)
  have hB : ContinuousOn B K := continuousOn_const.clm_comp
    ((AdjointCoefficients.Constructions.projectiveWeightedFormOperator_smooth V e he n).continuousOn.mono hKU)
  obtain ⟨c, hc, hb⟩ := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricBounds.CM.Construction.positive_bilinear_uniform_lower_bound B hK hB
    (fun z hz u hu => AdjointCoefficients.Constructions.projectiveWeightedFormOperator_positive V e he n z (hKU hz) u hu)
  refine ⟨c, hc, fun z hz u => ?_⟩
  have h := hb z hz u
  change c * ‖u‖ * ‖u‖ ≤ inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z u) u at h
  simpa only [pow_two, mul_assoc] using h

theorem projectiveWeightedFormOperator_uniform_upper
    {K : Set (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K) (hKU : K ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K,
      ∀ u v : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n,
        |inner ℝ (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z u) v| ≤ C * ‖u‖ * ‖v‖ := by
  let B := fun z => (innerSL ℝ).comp (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z)
  have hB : ContinuousOn B K := continuousOn_const.clm_comp
    ((AdjointCoefficients.Constructions.projectiveWeightedFormOperator_smooth V e he n).continuousOn.mono hKU)
  exact AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricBounds.CM.Construction.bilinear_uniform_upper_bound B hK hB

end

end OAI.Analysis.HodgeTheory.Decomposition.CoordinateEstimates.Constructions
