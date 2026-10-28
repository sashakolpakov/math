import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChartTestDerivatives

/-! # Chart One Test Derivatives -/

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

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.chartFrameTest_covariantDerivativeOne (i : V.analyticSpace)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    h.projectiveCovariantCoordinateDerivative V e i 1
      (Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e 1 (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest V u e i 1 f hf hs a).val) z =
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 2
        (Holomorphic.GlobalFrameForms.holomorphicLineGlobalFrame u i 2 (h.covariantDerivativeOne ⊤ (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 1 f hf a))).extension z := by
  have heq : Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e 1 (Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest V u e i 1 f hf hs a).val =ᶠ[𝓝 z]
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e 1 ((Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 1 f hf a).val i).extension := by
    filter_upwards [(ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)).isOpen.mem_nhds hz] with y hy
    exact Holomorphic.ChartFrameTests.holomorphicLineChartFrameTest_coefficients_eq V u e i 1 f hf hs a hy
  have hd := h.projectiveCovariantCoordinateDerivative_congr V e i 1 _ _ heq
  have ho := h.covariantDerivativeOne_coordinates V e he ⊤ (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 1 f hf a) i
    (show z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (⊤ ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
      from ⟨hz.1, trivial, hz.2⟩)
  exact hd.trans (ho.trans (Holomorphic.ChartTestDerivatives.holomorphicLineGlobalFrame_coefficients V e i 2
    (h.covariantDerivativeOne ⊤ (Holomorphic.SupportedForms.holomorphicLineSmoothMul u ⊤ 1 f hf a)) hz).symm)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
