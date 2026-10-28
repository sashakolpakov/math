import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Reconstruction
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.MultiplierReal

/-! # Localized Representative -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.LocalizedRepresentative

noncomputable section

/-! A genuine local Schwartz representative reconstructs the exact original smooth bundle cutoff of the completed L² form. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem holomorphicMetric_smooth_localized_representative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (n : ℕ) (β : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hβ : HasCompactSupport β) (hβD : tsupport β ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (χ : V.analyticSpace → ℂ) (hχ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ χ)
    (hχs : tsupport χ ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hgβ : ∀ x ∈ tsupport β, g x = 1)
    (hχβ : ∀ x ∈ tsupport (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e β), χ x = 1)
    (v : Holomorphic.IntegralPairZero.HolomorphicFormL2With V h n)
    (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    (hq : q.toLp 2 volume = ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g ((HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i n χ hχ hχs) v)) :
    Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h n (Holomorphic.AntiSchwartzTests.holomorphicLineSchwartzFrameInsertion V u e he i β hβ hβD n q) =
      Holomorphic.Multiplier.holomorphicMetricL2Multiplier V h n (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e β) (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_smooth V e he β hβ (fun _ hx => (hβD hx).1)) v :=
  Eq.trans (Holomorphic.ChartInsertion.holomorphicMetricChartL2Insertion_on_schwartz V h e he i n β hβ hβD q).symm
    (Eq.trans (congrArg (Holomorphic.ChartInsertion.holomorphicMetricChartL2Insertion V h e he i n β hβ hβD) hq)
      (Eq.trans (Holomorphic.ChartInsertion.holomorphicMetricChartL2Insertion_absorb V h e he i n β hβ hβD g hgβ ((HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i n χ hχ hχs) v))
        (Eq.trans (Holomorphic.Reconstruction.holomorphicMetricChartL2Insertion_localization V h e he i n β hβ hβD χ hχ hχs v)
          (Holomorphic.MultiplierReal.holomorphicMetricL2Multiplier_absorb V h n (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e β) χ (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_smooth V e he β hβ (fun _ hx => (hβD hx).1)) hχ hχβ v))))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.LocalizedRepresentative
