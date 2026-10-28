import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChartFrameTests
import OAI.AlgebraicGeometry.DivisorClass.Chern.CovariantBundleCoordinates

/-! # Chart Test Derivatives -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Compact frame tests retain the exact original bundle connection under differentiation. -/

open _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovariantCoordinateDerivative_congr (i : V.analyticSpace) (n : ℕ)
    (a b : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hab : a =ᶠ[𝓝 z] b) :
    h.projectiveCovariantCoordinateDerivative V e i n a z = h.projectiveCovariantCoordinateDerivative V e i n b z := by
  unfold HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovariantCoordinateDerivative Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.firstOrderCoordinateOperator
  rw [hab.fderiv_eq, hab.eq_of_nhds]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovariantCoordinateDerivative_zero_off_support (i : V.analyticSpace) (n : ℕ)
    (a : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V} (hz : z ∉ tsupport a) :
    h.projectiveCovariantCoordinateDerivative V e i n a z = 0 := by
  unfold HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovariantCoordinateDerivative Analysis.HodgeTheory.Decomposition.LocalAdjoint.Constructions.firstOrderCoordinateOperator
  rw [fderiv_of_notMem_tsupport ℝ hz, image_eq_zero_of_notMem_tsupport hz]
  simp only [_root_.zero_apply, map_zero, Finset.sum_const_zero, add_zero]

theorem Holomorphic.ChartTestDerivatives.holomorphicLineGlobalFrame_coefficients (i : V.analyticSpace) (n : ℕ)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e n (Holomorphic.GlobalFrameForms.holomorphicLineGlobalFrame u i n a).extension z =
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e n (a.val i).extension z := by
  unfold Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm
  rw [Holomorphic.GlobalFrameForms.holomorphicLineGlobalFrame_inChart u i n a e hz.2]

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.chartFrameTest_covariantDerivative (i : V.analyticSpace)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 0) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    h.projectiveCovariantCoordinateDerivative V e i 0
      (Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e 0 (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest V u e i 0 f hf hs a).val) z =
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 1
        (Holomorphic.GlobalFrameForms.holomorphicLineGlobalFrame u i 1 (h.covariantDerivative ⊤ (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 0 f hf a))).extension z := by
  have heq : Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e 0 (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest V u e i 0 f hf hs a).val =ᶠ[𝓝 z]
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 0 ((Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 0 f hf a).val i).extension := by
    filter_upwards [(ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen.mem_nhds hz] with y hy
    exact Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest_coefficients_eq V u e i 0 f hf hs a hy
  have hd := h.projectiveCovariantCoordinateDerivative_congr V e i 0 _ _ heq
  have ho := h.covariantDerivative_coordinates V e he ⊤ (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 0 f hf a) i
    (show z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (⊤ ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
      from ⟨hz.1, trivial, hz.2⟩)
  exact hd.trans (ho.trans (Holomorphic.ChartTestDerivatives.holomorphicLineGlobalFrame_coefficients V e i 1
    (h.covariantDerivative ⊤ (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 0 f hf a)) hz).symm)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
