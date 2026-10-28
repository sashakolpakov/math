import OAI.AlgebraicGeometry.DivisorClass.Chern.ZeroCovectorMetric
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.GlobalPairCoordinates

/-! # Zero Chart Pair -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Exact local scalar coefficients of original smooth line sections, with the original bundle metric and chart volume density. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (i : V.analyticSpace)

def Holomorphic.ZeroChartPair.holomorphicLineZeroChart (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : ℂ :=
  Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 0 (a.val i).extension z 0

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveGlobalPair_zero_self (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    (h.projectiveGlobalPair V e 0 a a z).re =
      (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z * (h.projectiveWeightChart V e i z).re) *
        ‖Holomorphic.ZeroChartPair.holomorphicLineZeroChart V e i a z‖ ^ 2 := by
  rw [h.projectiveGlobalPair_inFrame V e he 0 a a i hz, ZeroCovectorMetric.bilinearFormMetricPair_degree_zero,
    ← Complex.normSq_eq_conj_mul_self, h.projectiveWeightChart_apply V e i hz]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.normSq_eq_norm_sq, Holomorphic.ZeroChartPair.holomorphicLineZeroChart, mul_assoc]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveZeroChart_compact_lower (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    {K : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hK : IsCompact K)
    (hs : K ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, ∀ a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0,
      c * ‖Holomorphic.ZeroChartPair.holomorphicLineZeroChart V e i a z‖ ^ 2 ≤ (h.projectiveGlobalPair V e 0 a a z).re := by
  let q := fun z => ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z * (h.projectiveWeightChart V e i z).re
  have hq : ContinuousOn q K :=
    ((ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_smooth V e he).continuousOn.mono (fun _ hz => (hs hz).1)).mul
      (Complex.continuous_re.comp_continuousOn ((h.projectiveWeightChart_smooth V e he i).continuousOn.mono hs))
  obtain ⟨c, hc, hb⟩ := hK.exists_forall_le' hq (a := (0 : ℝ)) (by
    intro z hz
    dsimp only [q]
    rw [h.projectiveWeightChart_apply V e i (hs hz), Complex.ofReal_re]
    exact mul_pos (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_pos V e he (hs hz).1) (h.positive i _))
  refine ⟨c, hc, fun z hz a => ?_⟩
  rw [h.projectiveGlobalPair_zero_self V e he i a (hs hz)]
  exact mul_le_mul_of_nonneg_right (hb z hz) (sq_nonneg _)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
