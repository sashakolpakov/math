import OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorMetricCutoffBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CutoffCoordinates

/-! # Product Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric

noncomputable section

/-! A literal chart product identity gives the corresponding original global metric bound. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace)

include he

theorem Data.HolomorphicLineMetricData.globalFormPair_bound_of_chart_product (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) (c d : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (r : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n) (g : ℂ) (C K : ℝ)
    (hc : Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (c.val i).extension z = r + g • Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (d.val i).extension z)
    (hr : (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
      (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) r r).re ≤ C *
        (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1
          (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension z)
            (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension z)).re)
    (hg : ‖g‖ ^ 2 ≤ K) :
    (h.globalFormPair V n c c (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)).re ≤
      (2 * C) * (h.globalFormPair V 1 a a (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)).re +
        (2 * K) * (h.globalFormPair V n d d (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z)).re := by
  have hb := CovectorMetricCutoffBound.bilinearFormMetricPair_cutoff_bound (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hz.1)
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hz.1) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension z)
    r (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (d.val i).extension z) g C K hr hg
  have hq := (congrArg (fun v : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) n =>
    (Analysis.HodgeTheory.Decomposition.BilinearFormMetric.Constructions.bilinearFormMetricPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) v v).re) hc).trans_le hb
  have hw := mul_le_mul_of_nonneg_left hq (h.positive i ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z, hz.2⟩).le
  rw [h.globalFormPair_re_chart V e he i n c c hz,
    h.globalFormPair_re_chart V e he i 1 a a hz, h.globalFormPair_re_chart V e he i n d d hz]
  exact hw.trans_eq (by ring)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric
