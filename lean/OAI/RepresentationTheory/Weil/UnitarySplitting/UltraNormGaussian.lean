import OAI.RepresentationTheory.Weil.UnitarySplitting.NormCutoffScaling
import OAI.RepresentationTheory.Weil.UnitarySplitting.NormAdditiveMeasure
import OAI.RepresentationTheory.Weil.UnitarySplitting.CharacterTailCancellation

/-! # Ultra Norm Gaussian -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.UltraNormGaussian.Construction

noncomputable section

/-! The norm Gaussian has an exactly stable compact cutoff in the
nonarchimedean case. Its dependence on a nonzero coefficient is the given
quadratic character divided by the additive Haar modulus. -/

open _root_.MeasureTheory _root_.Topology
open scoped NNReal ENNReal

def normGaussianCutoff
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [MeasurableSpace E] (μ : Measure E) (ψ : AddChar F ℂ) (a : F) (r : ℝ) : ℂ :=
  ∫ b, (Metric.closedBall (0 : F) r).indicator (fun x => ψ x) (a * Algebra.norm F b) ∂μ

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
variable [CompleteSpace F] [LocallyCompactSpace F] [LocallyCompactSpace E] [FiniteDimensional F E]
variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace E] [BorelSpace E] [CharZero F]
variable [IsUltrametricDist F]
variable (hF : ¬ DiscreteTopology F) (hE : ¬ DiscreteTopology E)
variable (hEmbedding : Continuous (algebraMap F E)) (hQuadratic : Module.finrank F E = 2)
variable (σ : E ≃ₐ[F] E) (hne : ∃ z : E, σ z ≠ z)
variable (ω : Fˣ →ₜ* Circle) (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)

include hF hE hEmbedding hQuadratic hne hω in
omit [IsUltrametricDist F] in
theorem normGaussianCutoff_eq_norm_image_integral
    (μF : Measure F) [μF.IsAddHaarMeasure] [μF.Regular]
    (μE : Measure E) [μE.IsAddHaarMeasure] [μE.Regular]
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x)) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ r : ℝ, normGaussianCutoff μE ψ 1 r =
      (c : ℂ) * ∫ x in Metric.closedBall 0 r ∩ Set.range (Algebra.norm F : E → F), ψ x ∂μF := by
  obtain ⟨c, hcpos, hcomp⟩ := NormAdditiveMeasure.Construction.norm_additive_measure_comparison
    hF hE hEmbedding hQuadratic σ hne ω hω μF μE
  refine ⟨c, hcpos, fun r => ?_⟩
  have hf : StronglyMeasurable ((Metric.closedBall (0 : F) r).indicator (fun x => ψ x)) :=
    hc.stronglyMeasurable.indicator measurableSet_closedBall
  have hh := congrArg (fun ν : Measure F =>
    ∫ x, (Metric.closedBall (0 : F) r).indicator (fun x => ψ x) x ∂ν) hcomp
  rw [integral_map_of_stronglyMeasurable (QuadraticNorm.Construction.fieldNorm_continuous hF hEmbedding).measurable hf,
    integral_smul_nnreal_measure, setIntegral_indicator measurableSet_closedBall,
    Set.inter_comm] at hh
  simpa only [normGaussianCutoff, one_mul, NNReal.smul_def, Complex.real_smul] using hh

include hF hE hEmbedding hQuadratic hne hω in
theorem ultra_norm_gaussian_stable
    (μF : Measure F) [μF.IsAddHaarMeasure] [μF.Regular]
    (μE : Measure E) [μE.IsAddHaarMeasure] [μE.Regular]
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x)) (hn : ∃ t : F, ψ t ≠ 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r → ∀ a : Fˣ,
      (FieldModulus.Construction.fieldModulus F a : ℂ) * normGaussianCutoff μE ψ (a : F) r =
        (ω a : ℂ) * normGaussianCutoff μE ψ 1 R := by
  let : ProperSpace F := TestSpaceAnalysis.Construction.localField_proper F hF
  obtain ⟨t, ht⟩ := hn
  obtain ⟨R, hR, htR, htrans⟩ := NormAdditiveMeasure.Construction.quadratic_norm_mem_iff_translate_far hQuadratic ω hω t
  obtain ⟨c, -, hformula⟩ := normGaussianCutoff_eq_norm_image_integral
    hF hE hEmbedding hQuadratic σ hne ω hω μF μE ψ hc
  have hS : MeasurableSet (Set.range (Algebra.norm F : E → F)) :=
    (NormHaar.Construction.quadraticNorm_isProperMap hF hEmbedding hQuadratic).isClosed_range.measurableSet
  have hstable (r : ℝ) (hr : R ≤ r) : normGaussianCutoff μE ψ 1 r = normGaussianCutoff μE ψ 1 R := by
    rw [hformula, hformula, CharacterTailCancellation.Construction.ultra_character_cutoff_stable_on_set μF ψ hc t ht _ hS R htR htrans r hr]
  refine ⟨R, hR, fun r hr a => ?_⟩
  have hh := NormCutoffScaling.Construction.norm_character_cutoff_scaling hF hE hEmbedding hQuadratic σ hne ω hω
    μF μE ψ hc t ht r (htR.trans hr) a
  have hh' : (FieldModulus.Construction.fieldModulus F a : ℂ) * normGaussianCutoff μE ψ (a : F) r =
      (ω a : ℂ) * normGaussianCutoff μE ψ 1 r := by
    simpa only [normGaussianCutoff, one_mul] using hh
  rw [hstable r hr] at hh'
  exact hh'

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.UltraNormGaussian.Construction
