import OAI.AlgebraicGeometry.DivisorClass.Chern.ScalarChartReconstruction
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.TestScalar
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SchwartzTestCutoff
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChartScalarSupport
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Schwartz

/-! # Schwartz Reconstruction -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SchwartzReconstruction

noncomputable section

/-! Reconstructing original localized Schwartz coordinates equals the exact two original bundle cutoffs. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem holomorphicLineSchwartzFrameInsertion_localization (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (n : ℕ) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g) (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (χ : V.analyticSpace → ℂ) (hχ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ χ)
    (hχs : tsupport χ ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    AntiSchwartzTests.holomorphicLineSchwartzFrameInsertion V u e he i g hg hs n (HolomorphicFrame.Schwartz.holomorphicLineFrameCoefficientsSchwartz V e he i n χ hχ hχs a) =
      SupportedForms.holomorphicLineSmoothMul u ⊤ n (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e g) (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_smooth V e he g hg (fun _ hx => (hs hx).1)) (SupportedForms.holomorphicLineSmoothMul u ⊤ n χ hχ a) :=
  Eq.trans
    (congrArg (HolomorphicFrame.Insertion.holomorphicLineSmoothFrameInsertion u i n (AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs) (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs) (fun _ hx => (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs hx).2))
      (Eq.trans (ScalarChartReconstruction.projectiveSchwartzTestLocalized_reconstruct_coefficients V e he n g hg
        (fun _ hx => (hs hx).1) (ChartFrameTests.holomorphicLineChartFrameTest V u e i n χ hχ hχs a) (HolomorphicFrame.Schwartz.holomorphicLineFrameCoefficientsSchwartz V e he i n χ hχ hχs a) (fun _ => rfl))
        (HolomorphicFrame.TestScalar.holomorphicLineChartFrameTest_mul_right V e i n χ hχ hχs (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e g) (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_smooth V e he g hg (fun _ hx => (hs hx).1)) (ChartScalarSupport.varietyChartTestScalar_holomorphic_support V u e i g hg hs) a)))
    (Eq.trans (SchwartzTestCutoff.holomorphicLineSmoothFrameInsertion_chart_test V e i n (AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs) (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs) (fun _ hx => (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs hx).2)
      (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e g) (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_smooth V e he g hg (fun _ hx => (hs hx).1)) (ChartScalarSupport.varietyChartTestScalar_holomorphic_support V u e i g hg hs) (SupportedForms.holomorphicLineSmoothMul u ⊤ n χ hχ a))
      (SchwartzTestCutoff.holomorphicLineSmoothMul_nested V n (AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs) (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs) (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e g) (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_smooth V e he g hg (fun _ hx => (hs hx).1))
        (ChartScalarSupport.holomorphicSchwartzFrameCutoff_one_on_chart_scalar V u e i g hg hs he) (SupportedForms.holomorphicLineSmoothMul u ⊤ n χ hχ a)))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SchwartzReconstruction
