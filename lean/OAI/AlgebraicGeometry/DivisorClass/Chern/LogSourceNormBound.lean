import OAI.AlgebraicGeometry.DivisorClass.Chern.PointLogWeightAway
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.PotentialChartPair

/-! # Log Source Norm Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.LogSourceNormBound

noncomputable section

/-! An original bundle form supported in a compact chart set away from the point has a uniform original logarithmic metric norm. -/

open _root_.MeasureTheory Set
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem projectivePointLogPotential_source_norm_bound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
    (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (x : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hx : x ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (m n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    {K : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K)
    (hKD : K ⊆ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (hxK : x ∉ K)
    (ha : ∀ y ∉ Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e '' K, h.globalFormPair V n a a y = 0) :
    ∃ M : ℝ, 0 < M ∧ ∀ (ε : ℝ) (hε : 0 < ε), ε ≤ 1 →
      ((h.withPotential (PointLogMetricSolver.projectivePointLogPotential V e he x hx m ε hε)).formIntegralPair V n a a).re ≤ M := by
  obtain ⟨C, hC, hb⟩ := PointLogWeightAway.projectivePointLogPotential_weight_away V e he x hx m hK hKD hxK
  refine ⟨max (C * (h.formIntegralPair V n a a).re) 1,
    lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun ε hε hε1 => ?_⟩
  let φ := PointLogMetricSolver.projectivePointLogPotential V e he x hx m ε hε
  have hp (y : V.analyticSpace) : ((h.withPotential φ).globalFormPair V n a a y).re ≤
      C * (h.globalFormPair V n a a y).re := by
    rw [h.withPotential_globalFormPair_re V φ n a a y]
    by_cases hy : y ∈ Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e '' K
    · obtain ⟨z, hz, rfl⟩ := hy
      exact mul_le_mul_of_nonneg_right (hb ε hε hε1 z hz) (h.globalFormPair_nonneg V n a _)
    · rw [ha y hy, Complex.zero_re, mul_zero, mul_zero]
  have hi : ((h.withPotential φ).formIntegralPair V n a a).re ≤ C * (h.formIntegralPair V n a a).re := by
    rw [(h.withPotential φ).formIntegralPair_re V n a a, h.formIntegralPair_re V n a a, ← integral_const_mul]
    exact integral_mono ((h.withPotential φ).globalFormPair_integrable V n a a).re
      ((h.globalFormPair_integrable V n a a).re.const_mul C) hp
  exact hi.trans (le_max_left _ _)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.LogSourceNormBound
