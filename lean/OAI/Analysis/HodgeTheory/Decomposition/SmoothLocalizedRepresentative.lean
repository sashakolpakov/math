import OAI.Analysis.HodgeTheory.Decomposition.ChartReconstruction
import OAI.Analysis.HodgeTheory.Decomposition.ChartTestAbsorption
import OAI.Analysis.HodgeTheory.Decomposition.ChartReconstructionSmooth
import OAI.Analysis.HodgeTheory.Decomposition.SmoothGlobal

/-! # Smooth Localized Representative -/

namespace OAI.Analysis.HodgeTheory.Decomposition.SmoothLocalizedRepresentative.Constructions

noncomputable section

/-! A smooth coefficient representative near the support of a manifold
cutoff reconstructs a genuine smooth representative of that L² cutoff. -/

open _root_.MeasureTheory Set
open scoped SchwartzMap _root_.Manifold ContDiff

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  [MeasurableSpace V.analyticSpace] [BorelSpace V.analyticSpace]
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

theorem exists_projective_smooth_localized_representative
    (u : Form.Constructions.ProjectiveL2Forms V n)
    (χ : V.analyticSpace → ℝ) (hχ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ χ)
    (hχs : tsupport χ ⊆ e.source)
    (g : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ))
    (c : 𝓢(AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n))
    (hc : c.toLp 2 volume = AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g (VectorEnergyLocalization.Constructions.projectiveVectorL2Localization V e he n χ hχ hχs u))
    (ρ : V.analyticSpace → ℝ) (hρ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℝ) ∞ ρ)
    (hρs : tsupport ρ ⊆ e.source)
    (hχρ : ∀ x ∈ tsupport ρ, χ x = 1)
    (hgρ : ∀ x ∈ tsupport ρ, g (MeasureVolume.Constructions.chartCoordinateForward V e x) = 1) :
    ∃ a : DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n,
      Form.Constructions.smoothToProjectiveL2 V n a = SmoothGlobal.Constructions.projectiveRealL2Multiplier V n ρ hρ u := by
  obtain ⟨β, hβc, hβρ, hβs, hβeq⟩ := ChartReconstructionSmooth.Constructions.exists_projective_chart_scalar_cutoff V e he ρ hρ hρs
  have hgβ : ∀ z ∈ tsupport β, g z = 1 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hβρ hz
    exact hgρ x hx
  have hρsupport : tsupport (fun x => (ρ x : ℂ)) = tsupport ρ := by
    apply congrArg closure
    ext x
    simp only [Function.mem_support]
    exact not_congr Complex.ofReal_eq_zero
  have hχβ : ∀ x ∈ tsupport (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartTestFunction.CM.Construction.varietyChartTestScalar V e β), (χ x : ℂ) = 1 := by
    intro x hx
    rw [hβeq, hρsupport] at hx
    rw [hχρ x hx, Complex.ofReal_one]
  refine ⟨ChartCoefficientFaithful.Constructions.projectiveSchwartzTestLocalized V e he n β hβc hβs c, ?_⟩
  rw [← ChartTestAbsorption.Constructions.projectiveChartTestL2_on_schwartz, hc,
    ChartTestAbsorption.Constructions.projectiveChartTestL2_absorb V e he n β hβc hβs g hgβ,
    ChartReconstruction.Constructions.projectiveChartTestL2_localization,
    SmoothGlobal.Constructions.projectiveL2Multiplier_absorb V n _ _ _ _ hχβ]
  simp only [hβeq, SmoothGlobal.Constructions.projectiveRealL2Multiplier]

end

end OAI.Analysis.HodgeTheory.Decomposition.SmoothLocalizedRepresentative.Constructions
