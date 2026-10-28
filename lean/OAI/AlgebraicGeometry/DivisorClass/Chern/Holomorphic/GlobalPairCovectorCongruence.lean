import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CutoffOne

/-! # Global Pair Covector Congruence -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Equality of actual chart covectors gives equality of the original global metric pairings at that point. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair_congr_left_of_covector (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (n : ℕ) (a b c : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (hab : Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val i).extension z = Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (b.val i).extension z) :
    h.globalFormPair V n a c (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) =
      h.globalFormPair V n b c (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) := by
  have ha := h.projectiveGlobalPair_inFrame V e he n a c i hz
  have hb := h.projectiveGlobalPair_inFrame V e he n b c i hz
  have hcoord := congrArg (fun v : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n =>
    (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z : ℂ) * (h.projectiveWeightChart V e i z *
      Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
        (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) v (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (c.val i).extension z))) hab
  have hpair := ha.trans (hcoord.trans hb.symm)
  have hρ : (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z : ℂ) ≠ 0 := by
    exact_mod_cast (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_pos V e he hz.1).ne'
  exact mul_left_cancel₀ hρ hpair

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
