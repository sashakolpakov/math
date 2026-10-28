import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChartInsertion
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SchwartzReconstruction
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Multiplier

/-! # Reconstruction -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Reconstruction

noncomputable section

/-! Bounded chart reconstruction of the original L² localization equals exactly the two original bundle cutoff multipliers. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem holomorphicMetricChartL2Insertion_localization (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (n : ℕ) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g) (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (χ : V.analyticSpace → ℂ) (hχ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ χ)
    (hχs : tsupport χ ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (v : IntegralPairZero.HolomorphicFormL2With V h n) :
    (ChartInsertion.holomorphicMetricChartL2Insertion V h e he i n g hg hs) ((HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i n χ hχ hχs) v) = (Multiplier.holomorphicMetricL2Multiplier V h n (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e g) (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_smooth V e he g hg (fun _ hx => (hs hx).1))) ((Multiplier.holomorphicMetricL2Multiplier V h n χ hχ) v) :=
  congrFun ((IntegralPairZero.holomorphicFormL2WithInclusion_dense V h n).equalizer
    ((ChartInsertion.holomorphicMetricChartL2Insertion V h e he i n g hg hs).continuous.comp (HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i n χ hχ hχs).continuous)
    ((Multiplier.holomorphicMetricL2Multiplier V h n (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e g) (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_smooth V e he g hg (fun _ hx => (hs hx).1))).continuous.comp (Multiplier.holomorphicMetricL2Multiplier V h n χ hχ).continuous)
    (funext (fun a =>
      Eq.trans (congrArg (ChartInsertion.holomorphicMetricChartL2Insertion V h e he i n g hg hs) (HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization_on_smooth V h e he i n χ hχ hχs a))
        (Eq.trans (congrArg (ChartInsertion.holomorphicMetricChartL2Insertion V h e he i n g hg hs) (HolomorphicFrame.Schwartz.holomorphicLineFrameCoefficientsSchwartz_toLp V e he i n χ hχ hχs a).symm)
          (Eq.trans (ChartInsertion.holomorphicMetricChartL2Insertion_on_schwartz V h e he i n g hg hs (HolomorphicFrame.Schwartz.holomorphicLineFrameCoefficientsSchwartz V e he i n χ hχ hχs a))
            (Eq.trans (congrArg (IntegralPairZero.holomorphicFormL2WithInclusion V h n) (SchwartzReconstruction.holomorphicLineSchwartzFrameInsertion_localization V u e he i n g hg hs χ hχ hχs a))
              (Eq.trans (congrArg (Multiplier.holomorphicMetricL2Multiplier V h n (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e g) (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_smooth V e he g hg (fun _ hx => (hs hx).1))) (Multiplier.holomorphicMetricL2Multiplier_on_smooth V h n χ hχ a))
                (Multiplier.holomorphicMetricL2Multiplier_on_smooth V h n (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e g) (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_smooth V e he g hg (fun _ hx => (hs hx).1)) (SupportedForms.holomorphicLineSmoothMul u ⊤ n χ hχ a))).symm)))))) v

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Reconstruction
