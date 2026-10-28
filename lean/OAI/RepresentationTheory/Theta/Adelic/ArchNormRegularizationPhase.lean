import OAI.RepresentationTheory.Weil.UnitarySplitting.ComplexGaussianRegularization
import OAI.RepresentationTheory.Weil.UnitarySplitting.QuadraticGaussianRegularization
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealGaussianPhase
import OAI.RepresentationTheory.Weil.UnitarySplitting.RealCharacter

/-! # Arch Norm Regularization Phase -/

namespace OAI.RepresentationTheory.Theta.Adelic.ArchNormRegularizationPhase

noncomputable section

/-! Real norm Gaussians with their actual Fourier regularizations and
explicit phase, retaining the normalization constant needed by AdelicTheta. -/

open _root_.MeasureTheory
open scoped InnerProductSpace NNReal

theorem arch_norm_regularization_phase
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [LocallyCompactSpace E] [FiniteDimensional F E] [MeasurableSpace E] [BorelSpace E]
    (e : ℝ ≃+* F) (he : Continuous e) (hEmbedding : Continuous (algebraMap F E))
    (hQuadratic : Module.finrank F E = 2)
    (ω : Fˣ →ₜ* Circle) (hω : Weil.UnitarySplitting.Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (ψ : AddChar F ℂ) (t : ℝ) (ht : t ≠ 0)
    (hψ : ∀ x : F, ψ x = Complex.exp (Complex.I * t * (e.symm x : ℂ))) :
    ∃ Γ : ℂ, Γ ≠ 0 ∧ (∀ a : Fˣ, ∃ Z : ℂ, Z ≠ 0 ∧
      Weil.UnitarySplitting.QuadraticGaussianRegularization.Construction.HasGaussianRegularization μ ψ (fun x => (a : F) * Algebra.norm F x) Z ∧
      Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase Z = (ω a : ℂ) * Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase Γ) ∧
      Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase Γ = Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase (Weil.UnitarySplitting.ComplexGaussianFourier.Construction.complexNormGaussianValue t) := by
  obtain ⟨k, hk, hki, -, hN⟩ := Weil.UnitarySplitting.ArchimedeanNormCoordinates.Construction.complex_coordinates_for_quadratic_extension e he hEmbedding hQuadratic
  let j : E ≃ₜ+ ℂ := { k.toAddEquiv with continuous_toFun := hk, continuous_invFun := hki }
  have hj (v : E) : j v = k v := rfl
  let ν : Measure ℂ := μ.map j
  let : ν.IsAddHaarMeasure := j.isAddHaarMeasure_map μ
  let c := Measure.addHaarScalarFactor ν (volume : Measure ℂ)
  have hc0 : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν volume
  have hν : ν = c • volume := Measure.isAddLeftInvariant_eq_smul_of_regular ν volume
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (show (c : ℝ) ≠ 0 from ne_of_gt hc0)
  let Γ : ℂ := (c : ℂ) * Weil.UnitarySplitting.ComplexGaussianFourier.Construction.complexNormGaussianValue t
  have hΓ : Γ ≠ 0 := mul_ne_zero hcC (Weil.UnitarySplitting.ComplexGaussianFourier.Construction.complexNormGaussianValue_ne_zero t ht)
  refine ⟨Γ, hΓ, ?_, ?_⟩
  swap
  · exact (Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase_mul (c : ℂ) (Weil.UnitarySplitting.ComplexGaussianFourier.Construction.complexNormGaussianValue t)).trans
      (by rw [Weil.UnitarySplitting.DiagonalNormGaussian.Construction.gaussianPhase_positive (c : ℝ) hc0, one_mul])
  intro a
  let s : ℝ := e.symm (a : F)
  have hs : s ≠ 0 := (map_ne_zero e.symm).mpr a.ne_zero
  let Z : ℂ := (c : ℂ) * Weil.UnitarySplitting.ComplexGaussianFourier.Construction.complexNormGaussianValue (t * s)
  have hZ : Z ≠ 0 := mul_ne_zero hcC (Weil.UnitarySplitting.ComplexGaussianFourier.Construction.complexNormGaussianValue_ne_zero (t * s) (mul_ne_zero ht hs))
  have hZeq : Z = Γ / (s : ℂ) := by
    dsimp only [Z, Γ, Weil.UnitarySplitting.ComplexGaussianFourier.Construction.complexNormGaussianValue]
    rw [Complex.ofReal_mul]
    field_simp
  refine ⟨Z, hZ, ?_, ?_⟩
  · have R₀ := (Weil.UnitarySplitting.ComplexGaussianRegularization.Construction.complexNormGaussianRegularization (t * s) (mul_ne_zero ht hs)).smul_measure c hc0
    have Rν : Weil.UnitarySplitting.ComplexGaussianFourier.Construction.GaussianFourierRegularization ν
        (fun z => Complex.exp (Complex.I * (t * s : ℝ) * (Complex.normSq z : ℂ)))
        (fun w => Complex.exp (-Complex.I * (t * s : ℝ) * (Complex.normSq w : ℂ)))
        (fun z w => Complex.exp (2 * Complex.I * (t * s : ℝ) * (inner ℝ w z : ℂ))) Z := hν.symm ▸ R₀
    have R := Rν.homeomorph j.toHomeomorph rfl
    have hphase : (fun v : E => Complex.exp (Complex.I * (t * s : ℝ) * (Complex.normSq (j v) : ℂ))) =
        (fun v => ψ ((a : F) * Algebra.norm F v)) := by
      funext v
      rw [hψ, map_mul, hN, Complex.ofReal_mul, Complex.ofReal_mul]
      congr 1
      change Complex.I * ((t : ℂ) * (s : ℂ)) * _ = Complex.I * t * ((s : ℂ) * _)
      simp only [hj]
      ring
    have hdual : (fun w : E => Complex.exp (-Complex.I * (t * s : ℝ) * (Complex.normSq (j w) : ℂ))) =
        (fun w => ψ (-((a : F) * Algebra.norm F w))) := by
      funext w
      rw [hψ, map_neg, map_mul, hN, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_mul]
      congr 1
      change -Complex.I * ((t : ℂ) * (s : ℂ)) * _ = Complex.I * t * (-((s : ℂ) * _))
      simp only [hj]
      ring
    have hkernel : (fun v w : E => Complex.exp (2 * Complex.I * (t * s : ℝ) * (inner ℝ (j w) (j v) : ℂ))) =
        (fun v w => ψ ((a : F) * Algebra.norm F (v + w) - (a : F) * Algebra.norm F v -
          (a : F) * Algebra.norm F w)) := by
      funext v w
      rw [hψ, map_sub, map_sub, map_mul, map_mul, map_mul, hN, hN, hN, map_add,
        Complex.normSq_add, Complex.inner]
      simp only [Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_ofNat]
      congr 1
      change 2 * Complex.I * ((t : ℂ) * (s : ℂ)) * _ =
        Complex.I * t * ((s : ℂ) * (_ + _ + 2 * _) - (s : ℂ) * _ - (s : ℂ) * _)
      simp only [hj]
      ring
    exact ⟨hphase ▸ hdual ▸ hkernel ▸ R⟩
  · rw [hZeq]
    exact Weil.UnitarySplitting.RealGaussianPhase.Construction.archimedean_gaussian_phase_scaling e k hN hQuadratic ω hω Γ a

end

end OAI.RepresentationTheory.Theta.Adelic.ArchNormRegularizationPhase
