import OAI.RepresentationTheory.Weil.Local.RealOscillator
import OAI.RepresentationTheory.Weil.Local.SiegelGaussian

/-! # Real Generators -/

namespace OAI.RepresentationTheory.Weil.Local.RealGenerators.Construction

noncomputable section

/-! Concrete multiplication and Fourier formulas for the extended real oscillator action. -/

open _root_.MeasureTheory
open scoped InnerProductSpace ComplexConjugate

theorem real_memLp_reference_of_volume {n : ℕ} {f : FunctionsMetaplectic.Construction.Position ℝ n → ℂ} (hf : MemLp f 2) :
    MemLp f 2 (UnitaryInner.Construction.referencePositionMeasure ℝ n) := by
  rw [Measure.isAddLeftInvariant_eq_smul_of_regular (UnitaryInner.Construction.referencePositionMeasure ℝ n) volume]
  exact hf.smul_measure (by simp)

theorem inner_mul_unit_scalar (z f g : ℂ) (hz : ‖z‖ = 1) :
    ⟪z * f, z * g⟫_ℂ = ⟪f, g⟫_ℂ := by
  simp only [RCLike.inner_apply, map_mul]
  calc
    _ = (z * conj z) * (g * conj f) := by ring
    _ = _ := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; simp

theorem realL2Oscillator_multiplier {n : ℕ} (ψ : AddChar ℝ ℂ) (a : FunctionsMetaplectic.Construction.Oscillator ℝ n ψ)
    (q : FunctionsMetaplectic.Construction.Position ℝ n → ℂ) (hq : ∀ x, ‖q x‖ = 1)
    (ha : ∀ (φ : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) x, (a.val.2 φ).val x = q x * φ.val x)
    {f g : FunctionsMetaplectic.Construction.Position ℝ n → ℂ}
    (hf : MemLp f 2 (UnitaryInner.Construction.referencePositionMeasure ℝ n))
    (hg : MemLp g 2 (UnitaryInner.Construction.referencePositionMeasure ℝ n))
    (hfg : ∀ x, g x = q x * f x) :
    RealOscillator.Construction.realL2Oscillator n ψ a (hf.toLp f) = hg.toLp g := by
  apply RealOscillator.Construction.realL2Oscillator_toLp_eq_of_integrals
  intro φ
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [hfg, ha, inner_mul_unit_scalar _ _ _ (hq x)]

theorem real_standard_fourier_oscillator_apply {n : ℕ} (φ : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n)
    (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    ((RealFourierFamily.Construction.realFourierOscillatorFamily n 1 one_ne_zero).val.2 φ).val x =
      FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) volume φ.val x := by
  change (RealFourierFamily.Construction.realNormalizedFourier n 1 one_ne_zero φ).val x = _
  rw [RealFourierFamily.Construction.realNormalizedFourier_apply, RealNormalization.Construction.fourierIntegral_real_normalized 1 one_ne_zero]
  simp

theorem realL2Oscillator_fourier {n : ℕ} {f g : FunctionsMetaplectic.Construction.Position ℝ n → ℂ}
    (hfi : Integrable f)
    (hf : MemLp f 2 (UnitaryInner.Construction.referencePositionMeasure ℝ n))
    (hg : MemLp g 2 (UnitaryInner.Construction.referencePositionMeasure ℝ n))
    (hfg : ∀ x, g x = FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) volume f x) :
    RealOscillator.Construction.realL2Oscillator n (Gaussian.Construction.realCharacter 1) (RealFourierFamily.Construction.realFourierOscillatorFamily n 1 one_ne_zero)
      (hf.toLp f) = hg.toLp g := by
  apply RealOscillator.Construction.realL2Oscillator_toLp_eq_of_integrals
  intro φ
  rw [Measure.isAddLeftInvariant_eq_smul_of_regular (UnitaryInner.Construction.referencePositionMeasure ℝ n) volume,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  congr 1
  let a := RealFourierFamily.Construction.realFourierOscillatorFamily n 1 one_ne_zero
  have ha : (a.val.2 φ).val = FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) volume φ.val :=
    funext (real_standard_fourier_oscillator_apply φ)
  have hs := NonarchimedeanFourier.Construction.fourierIntegral_inner_swap (Gaussian.Construction.realCharacter 1) (QuadraticIntertwiner.Construction.realCharacter_unitary 1)
    (RealTestSpace.Construction.realCharacter_temperate 1).1.continuous volume hfi (FunctionsMetaplectic.Construction.schwartzBruhat_integrable volume (a.val.2 φ))
  have hFF (x : FunctionsMetaplectic.Construction.Position ℝ n) : FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) volume (a.val.2 φ).val (-x) = φ.val x := by
    rw [ha, RealFourierLp.Construction.real_fourier_inversion_standard, neg_neg]
  simp_rw [← hfg, hFF] at hs
  exact hs.symm

theorem realL2Oscillator_scalar_multiple {n : ℕ} (ψ : AddChar ℝ ℂ)
    (a b : FunctionsMetaplectic.Construction.Oscillator ℝ n ψ) (z : ℂ)
    (h : ∀ φ : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n, a.val.2 φ = z • b.val.2 φ)
    (f : Lp ℂ 2 (UnitaryInner.Construction.referencePositionMeasure ℝ n)) :
    RealOscillator.Construction.realL2Oscillator n ψ a f = z • RealOscillator.Construction.realL2Oscillator n ψ b f := by
  have he := (RealOscillator.Construction.real_testToL2_dense n).equalizer (RealOscillator.Construction.realL2Oscillator n ψ a).continuous
    (by fun_prop : Continuous (fun v => z • RealOscillator.Construction.realL2Oscillator n ψ b v))
    (show RealOscillator.Construction.realL2Oscillator n ψ a ∘ UnitaryInner.Construction.testToL2 ℝ n =
      (fun v => z • RealOscillator.Construction.realL2Oscillator n ψ b v) ∘ UnitaryInner.Construction.testToL2 ℝ n from by
        funext φ
        change RealOscillator.Construction.realL2Oscillator n ψ a (UnitaryInner.Construction.testToL2 ℝ n φ) = z • RealOscillator.Construction.realL2Oscillator n ψ b (UnitaryInner.Construction.testToL2 ℝ n φ)
        rw [RealOscillator.Construction.realL2Oscillator_apply, RealOscillator.Construction.realL2Oscillator_apply, h, map_smul])
  exact congrFun he f

end

end OAI.RepresentationTheory.Weil.Local.RealGenerators.Construction
