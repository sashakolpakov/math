import OAI.AlgebraicGeometry.DivisorClass.Chern.PointLogMetricSolver
import OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedLogParameterSmooth

/-! # Point Log Weight Away -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.PointLogWeightAway

noncomputable section

/-! The actual logarithmic point metric weights are uniformly bounded on compact coordinate sets avoiding the point. -/

open Set
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem projectivePointLogPotential_weight_away (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hx : x ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (m : ℕ)
    {K : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K)
    (hKD : K ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (hxK : x ∉ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 → ∀ z ∈ K,
      Real.exp (ScalarPotentialFunctions.realPotentialScalar (PointLogMetricSolver.projectivePointLogPotential V e he x hx m ε hε)
        (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)) ≤ C := by
  let η := PointLogCutoff.projectivePointLogCutoff V e x hx
  let F : ℝ × ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℝ := fun p => Real.exp (η p.2 * RegularizedLogWeight.regularizedNegativeLog x m p.1 p.2)
  have hF : ContinuousOn F (Icc (0 : ℝ) 1 ×ˢ K) :=
    Real.continuous_exp.comp_continuousOn
      ((RegularizedLogParameterSmooth.regularizedLogCutoff_parameter_smooth x m η (PointLogCutoff.projectivePointLogCutoff_smooth V e x hx)).continuousOn.mono
        (RegularizedLogParameterSmooth.regularizedLogSmoothDomain_contains x hxK))
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod hK).bddAbove_image hF
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun ε hε hε1 z hz => ?_⟩
  have hb := (hB (mem_image_of_mem F (show (ε, z) ∈ Icc (0 : ℝ) 1 ×ˢ K from ⟨⟨hε.le, hε1⟩, hz⟩))).trans
    (le_max_left B 1)
  have hv : ScalarPotentialFunctions.realPotentialScalar (PointLogMetricSolver.projectivePointLogPotential V e he x hx m ε hε)
      (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) = η z * RegularizedLogWeight.regularizedNegativeLog x m ε z := by
    exact (Projective.LogPointPotential.projectiveLogPointPotential_scalar V e he _ _ _ _ x m ε hε (e.map_target (hKD hz))).trans
      (congrArg (fun w => η w * RegularizedLogWeight.regularizedNegativeLog x m ε w) (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward_inverse V e z (hKD hz)))
  rw [hv]
  exact hb

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.PointLogWeightAway
