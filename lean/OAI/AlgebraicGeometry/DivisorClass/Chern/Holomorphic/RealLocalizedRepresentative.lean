import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.LocalizedRepresentative
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.MultiplierReal
import OAI.Analysis.HodgeTheory.Decomposition.ChartReconstructionSmooth

/-! # Real Localized Representative -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.RealLocalizedRepresentative

noncomputable section

/-! Every sufficiently small original real manifold cutoff reconstructs a genuine smooth bundle representative from the actual local Schwartz coefficients. -/

open _root_.TopologicalSpace _root_.MeasureTheory Set
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.ChartReconstructionSmooth.Constructions

theorem holomorphicMetric_smooth_real_localized_representative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (n : ℕ) (v : IntegralPairZero.HolomorphicFormL2With V h n)
    (χ : V.analyticSpace → ℂ) (hχ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ χ)
    (hχs : tsupport χ ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ))
    (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    (hq : q.toLp 2 volume = ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g (HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i n χ hχ hχs v))
    (ρ : V.analyticSpace → ℝ) (hρ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ ρ)
    (hρs : tsupport ρ ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (hχρ : ∀ x ∈ tsupport ρ, χ x = 1)
    (hgρ : ∀ x ∈ tsupport ρ, g (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e x) = 1) :
    ∃ a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n,
      IntegralPairZero.holomorphicFormL2WithInclusion V h n a = MultiplierReal.holomorphicMetricRealL2Multiplier V h n ρ hρ v := by
  let B := Analysis.HodgeTheory.Decomposition.ChartReconstructionSmooth.Constructions.exists_projective_chart_scalar_cutoff V e he ρ hρ (fun _ hx => (hρs hx).1)
  let β := B.choose
  have hβ := B.choose_spec
  have hβD : tsupport β ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e
      (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i) := by
    intro z hz
    refine ⟨hβ.2.2.1 hz, ?_⟩
    obtain ⟨x, hx, rfl⟩ := hβ.2.1 hz
    change Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateForward V e x) ∈
      CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i
    rw [Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse_forward V e x (hρs hx).1]
    exact (hρs hx).2
  have hgβ : ∀ z ∈ tsupport β, g z = 1 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hβ.2.1 hz
    exact hgρ x hx
  have hχβ : ∀ x ∈ tsupport (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e β), χ x = 1 := by
    intro x hx
    rw [hβ.2.2.2, MultiplierReal.realScalar_complex_tsupport] at hx
    exact hχρ x hx
  exact ⟨AntiSchwartzTests.holomorphicLineSchwartzFrameInsertion V u e he i β hβ.1 hβD n q,
    (HolomorphicSmooth.LocalizedRepresentative.holomorphicMetric_smooth_localized_representative V h e he i n β hβ.1 hβD χ hχ hχs g hgβ hχβ v q hq).trans
      (MultiplierReal.holomorphicMetricL2Multiplier_congr V h n (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e β) (fun x => (ρ x : ℂ))
        (ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar_smooth V e he β hβ.1 (fun _ hz => (hβD hz).1))
        (Complex.ofRealCLM.contDiff.contMDiff.comp hρ) hβ.2.2.2 v)⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.RealLocalizedRepresentative
