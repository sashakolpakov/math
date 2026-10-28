import OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanGaussian
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealGaussianPhase
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealCharacter

/-! # Archimedean Norm Gaussian -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanNormGaussian.Construction

noncomputable section

/-! The actual regularized norm phase integral at a real place has a
nonzero boundary value and the required quadratic-character phase. -/

open _root_.MeasureTheory _root_.Topology Filter

def archNormGaussianRegularization
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E] [MeasurableSpace E]
    (e : ℝ ≃+* F) (μ : Measure E) (ψ : AddChar F ℂ) (a : F) (ε : ℝ) : ℂ :=
  ∫ x, Complex.exp (-(ε : ℂ) * (e.symm (Algebra.norm F x) : ℂ)) * ψ (a * Algebra.norm F x) ∂μ

theorem archimedean_norm_gaussian_formula
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [LocallyCompactSpace E] [FiniteDimensional F E] [MeasurableSpace E] [BorelSpace E]
    (e : ℝ ≃+* F) (he : Continuous e) (hEmbedding : Continuous (algebraMap F E))
    (hQuadratic : Module.finrank F E = 2)
    (ω : Fˣ →ₜ* Circle) (hω : Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x))
    (hu : ∀ x : F, ‖ψ x‖ = 1) (hn : ∃ x : F, ψ x ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ t : ℝ, t ≠ 0 ∧ ∀ a : Fˣ,
      (∀ ε : ℝ, 0 < ε → archNormGaussianRegularization e μ ψ (a : F) ε =
        (C : ℂ) / ((ε : ℂ) - Complex.I * t * (e.symm (a : F) : ℂ))) ∧
      Tendsto (archNormGaussianRegularization e μ ψ (a : F)) (𝓝[>] (0 : ℝ))
        (𝓝 ((C : ℂ) / (-Complex.I * t * (e.symm (a : F) : ℂ)))) ∧
      (C : ℂ) / (-Complex.I * t * (e.symm (a : F) : ℂ)) ≠ 0 ∧
      DiagonalNormGaussian.Construction.gaussianPhase ((C : ℂ) / (-Complex.I * t * (e.symm (a : F) : ℂ))) =
        (ω a : ℂ) * DiagonalNormGaussian.Construction.gaussianPhase ((C : ℂ) / (-Complex.I * t)) := by
  obtain ⟨k, hk, hki, -, hN⟩ := ArchimedeanNormCoordinates.Construction.complex_coordinates_for_quadratic_extension e he hEmbedding hQuadratic
  obtain ⟨C, hC, hGaussian⟩ := ArchimedeanGaussian.Construction.norm_gaussian_from_complex_coordinates k hk hki
    (fun x => e.symm (Algebra.norm F x)) hN μ
  obtain ⟨t, ht, hψ⟩ := RealCharacter.Construction.real_coordinate_character_frequency e he ψ hc hu hn
  refine ⟨C, hC, t, ht, fun a => ?_⟩
  have ha : e.symm (a : F) ≠ 0 := (map_ne_zero e.symm).mpr a.ne_zero
  have hformula (ε : ℝ) (hε : 0 < ε) : archNormGaussianRegularization e μ ψ (a : F) ε =
      (C : ℂ) / ((ε : ℂ) - Complex.I * t * (e.symm (a : F) : ℂ)) := by
    let b : ℂ := (ε : ℂ) - Complex.I * t * (e.symm (a : F) : ℂ)
    have hb : 0 < b.re := by simpa [b] using hε
    have heq : archNormGaussianRegularization e μ ψ (a : F) ε =
        ∫ x, Complex.exp (-b * (e.symm (Algebra.norm F x) : ℂ)) ∂μ := by
      unfold archNormGaussianRegularization
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [hψ, ← Complex.exp_add, map_mul, Complex.ofReal_mul]
        congr 1
        dsimp only [b]
        ring
    exact heq.trans (hGaussian b hb)
  refine ⟨hformula, ?_, ?_, ?_⟩
  · have hlim := ArchimedeanGaussian.Construction.gaussian_boundary_limit C (t * e.symm (a : F)) (mul_ne_zero ht ha)
    have hlim' : Tendsto (fun ε : ℝ => (C : ℂ) / ((ε : ℂ) - Complex.I * t * (e.symm (a : F) : ℂ)))
        (𝓝[>] (0 : ℝ)) (𝓝 ((C : ℂ) / (-Complex.I * t * (e.symm (a : F) : ℂ)))) := by
      simpa only [Complex.ofReal_mul, mul_assoc] using hlim
    apply hlim'.congr'
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hformula ε hε).symm
  · exact div_ne_zero (Complex.ofReal_ne_zero.mpr hC.ne')
      (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr ht))
        (Complex.ofReal_ne_zero.mpr ha))
  · rw [← div_div]
    exact RealGaussianPhase.Construction.archimedean_gaussian_phase_scaling e k hN hQuadratic ω hω _ a

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanNormGaussian.Construction
