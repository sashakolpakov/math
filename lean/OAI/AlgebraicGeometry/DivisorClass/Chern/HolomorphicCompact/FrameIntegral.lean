import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.ChartField
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.GlobalPairCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.TensorMetricTest
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AdjointPointPairs
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.MetricAdjoint
import OAI.Analysis.HodgeTheory.Decomposition.ChartIntegral

/-! # Frame Integral -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-! Exact metric pairings of the original bundle cutoff forms and their literal compact chart fields. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff ComplexConjugate
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.ChartIntegral.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace) (n : ℕ)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.globalFormPair_cutoff_zero
    (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) (x : V.analyticSpace) (hx : x ∉ tsupport f) :
    h.globalFormPair V n b (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a) x = 0 := by
  have hxx := (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts V.analyticModel V.analyticSpace u).mem_domain x
  rw [← h.globalFormPair_conj V n b _ x, h.globalFormPair_inFrame V n _ b x x hxx,
    Holomorphic.SupportedForms.holomorphicLineSmoothMul_apply, Projective.CovectorPair.projectiveTangentCovectorPair_smul_left,
    image_eq_zero_of_notMem_tsupport hx, map_zero, zero_mul, mul_zero, map_zero]

def HolomorphicMetric.Data.HolomorphicLineMetricData.compactFramePair (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → ℂ :=
  Line.TensorMetricTest.lineMetricTestPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e)
    (h.projectiveWeightChart V e i) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (b.val i).extension)
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i n f hf hs a)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactFramePair_tsupport (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    tsupport (h.compactFramePair V e i n f hf hs a b) ⊆
      ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) :=
  (Line.TensorMetricTest.lineMetricTestPair_tsupport _ _ _ _ _ _).trans (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_tsupport V e i n f hf hs a)

include he in
theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactFramePair_inFrame (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    h.compactFramePair V e i n f hf hs a b z =
      h.projectiveGlobalPair V e n b (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a) z := by
  rw [h.projectiveGlobalPair_inFrame V e he n b _ i hz]
  unfold HolomorphicMetric.Data.HolomorphicLineMetricData.compactFramePair Line.TensorMetricTest.lineMetricTestPair
  rw [HolomorphicCompact.ChartField.holomorphicLineCompactChartField_inFrame V e i n f hf hs a hz]
  exact mul_assoc _ _ _

include he in
theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactFramePair_on_base (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∈ ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    h.compactFramePair V e i n f hf hs a b z =
      h.projectiveGlobalPair V e n b (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a) z := by
  by_cases hi : Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i
  · exact h.compactFramePair_inFrame V e he i n f hf hs a b ⟨hz, hi⟩
  · have hc : h.compactFramePair V e i n f hf hs a b z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hi (h.compactFramePair_tsupport V e i n f hf hs a b ht).2)
    rw [hc, HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveGlobalPair, h.globalFormPair_cutoff_zero V n f hf a b _ (fun ht => hi (hs ht).2), mul_zero]

end

/-! Literal compact frame integrals equal the original global bundle pairing of cutoff forms. -/

open _root_.MeasureTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.ChartIntegral.Constructions

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace) (n : ℕ)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.compactFramePair_integral (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    (∫ z, h.compactFramePair V e i n f hf hs a b z) =
      h.formIntegralPair V n b (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a) := by
  let Φ := h.globalFormPair V n b (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a)
  have hzero (x : V.analyticSpace) (hx : x ∉ e.source) : Φ x = 0 :=
    h.globalFormPair_cutoff_zero V n f hf a b x (fun ht => hx (hs ht).1)
  have hchart := Analysis.HodgeTheory.Decomposition.ChartIntegral.Constructions.projectiveMetricVolume_integral_chart V e he Φ
    (h.globalFormPair_smooth V n b _).continuous.aestronglyMeasurable hzero
  calc
    _ = ∫ z in ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e, h.compactFramePair V e i n f hf hs a b z := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      exact image_eq_zero_of_notMem_tsupport (fun ht => hz (h.compactFramePair_tsupport V e i n f hf hs a b ht).1)
    _ = ∫ z in ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e, ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z • Φ (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) := by
      apply setIntegral_congr_fun (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.measurableSet
      intro z hz
      rw [h.compactFramePair_on_base V e he i n f hf hs a b hz]
      exact Complex.real_smul.symm
    _ = ∫ x, Φ x ∂ Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.projectiveMetricVolume V := hchart.symm
    _ = _ := by
      rw [Projective.MetricAdjoint.projectiveMetricVolume_eq_variety V]
      rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
