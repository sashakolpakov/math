import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.GlobalFrameForms
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SupportedForms
import OAI.Analysis.HodgeTheory.Decomposition.SupportedCoordinates
import OAI.Analysis.HodgeTheory.Decomposition.AdjointLocality

/-! # Chart Frame Tests -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChartFrameTests

noncomputable section

/-! Compactly supported tests in an original bundle frame, represented by genuine global scalar forms and chart coefficients. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (i : V.analyticSpace) (n : ℕ)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))

def holomorphicLineChartFrameTest (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtension f hf.contMDiffOn (fun _ hx => (hs hx).2)
    (GlobalFrameForms.holomorphicLineGlobalFrame u i n a)

theorem holomorphicLineChartFrameTest_apply (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (x : CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) :
    holomorphicLineChartFrameTest V u e i n f hf hs a x.val =
      f x.val • a.val i ⟨x.val, trivial, x.property⟩ := by
  rw [holomorphicLineChartFrameTest, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtension_apply_mem,
    GlobalFrameForms.holomorphicLineGlobalFrame_apply]

theorem holomorphicLineChartFrameTest_zero (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (x : V.analyticSpace) (hx : x ∉ tsupport f) :
    holomorphicLineChartFrameTest V u e i n f hf hs a x = 0 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.supportedExtension_eq_zero_of_notMem_tsupport f hf.contMDiffOn _ _ hx

theorem holomorphicLineChartFrameTest_coefficients_compact (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    HasCompactSupport (Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n (holomorphicLineChartFrameTest V u e i n f hf hs a).val) :=
  Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.supportedEuclideanCoefficients_compact V e n _ (isClosed_tsupport f).isCompact (fun _ hx => (hs hx).1)
    (holomorphicLineChartFrameTest_zero V u e i n f hf hs a)

theorem holomorphicLineChartFrameTest_coefficients_tsupport (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    tsupport (Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n (holomorphicLineChartFrameTest V u e i n f hf hs a).val) ⊆
      ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.supportedEuclideanCoefficients_tsupport V e n _
    (isClosed_tsupport f).isCompact (fun _ hy => (hs hy).1)
    (holomorphicLineChartFrameTest_zero V u e i n f hf hs a) hz
  refine ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward_mem V e x (hs hx).1, ?_⟩
  change Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e x) ∈ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i
  rw [Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse_forward V e x (hs hx).1]
  exact (hs hx).2

theorem holomorphicLineChartFrameTest_coefficients_eq (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n (holomorphicLineChartFrameTest V u e i n f hf hs a).val z =
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartCoefficients V e n ((SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a).val i).extension z := by
  rw [Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.supportedEuclideanCoefficients_eq V e n _ hz.1]
  apply Analysis.HodgeTheory.Decomposition.AdjointLocality.Constructions.euclideanChartCoefficients_congr_at V n e
  have hi : Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z ∈ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i := hz.2
  rw [holomorphicLineChartFrameTest_apply V u e i n f hf hs a ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z, hi⟩,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply ((SupportedForms.holomorphicLineSmoothMul u ⊤ n f hf a).val i)
      ⟨Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z, trivial, hi⟩,
    SupportedForms.holomorphicLineSmoothMul_apply]

include he

theorem holomorphicLineChartFrameTest_coefficients_smooth (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    ContDiff ℝ ∞ (Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.supportedEuclideanCoefficients V e n (holomorphicLineChartFrameTest V u e i n f hf hs a).val) :=
  Analysis.HodgeTheory.Decomposition.SupportedCoordinates.Constructions.supportedEuclideanCoefficients_smooth V e he n _ (isClosed_tsupport f).isCompact
    (fun _ hx => (hs hx).1) (holomorphicLineChartFrameTest_zero V u e i n f hf hs a)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChartFrameTests
