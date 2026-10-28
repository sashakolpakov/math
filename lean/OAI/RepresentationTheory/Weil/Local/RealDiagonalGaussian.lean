import OAI.RepresentationTheory.Weil.Local.RealFourierFamily
import OAI.RepresentationTheory.Weil.Local.FresnelLimit

/-! # Real Diagonal Gaussian -/

namespace OAI.RepresentationTheory.Weil.Local.RealDiagonalGaussian.Construction

noncomputable section

section

/-! Damped real quadratic phases and their Fourier limits. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology

def realQuadraticDamping (c ε x : ℝ) : ℂ :=
  (Real.exp (-ε * x ^ 2) : ℂ) * Gaussian.Construction.realCharacter c (x ^ 2 / 2)

theorem realQuadraticDamping_eq (c ε x : ℝ) :
    realQuadraticDamping c ε x =
      Complex.exp (-((ε : ℂ) - Real.pi * c * Complex.I) * (x : ℂ) ^ 2) := by
  rw [realQuadraticDamping, Gaussian.Construction.realCharacter_apply, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem realQuadraticDamping_integrable (c ε : ℝ) (hε : 0 < ε) :
    Integrable (realQuadraticDamping c ε) := by
  change Integrable (fun x => realQuadraticDamping c ε x)
  simp_rw [realQuadraticDamping_eq]
  exact integrable_cexp_neg_mul_sq (b := (ε : ℂ) - Real.pi * c * Complex.I)
    (by simpa using hε)

theorem scalarFourier_realQuadraticDamping (c ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    FourierTensor.Construction.scalarFourierIntegral (Gaussian.Construction.realCharacter c) volume (realQuadraticDamping c ε) x =
      Gaussian.Construction.realDampedGaussian c 1 ε *
        Complex.exp (-((Real.pi : ℂ) ^ 2 * c ^ 2 * x ^ 2) /
          ((ε : ℂ) - Real.pi * c * Complex.I)) := by
  unfold FourierTensor.Construction.scalarFourierIntegral
  simp_rw [realQuadraticDamping_eq, Gaussian.Construction.realCharacter_apply]
  have hk (y : ℝ) : (((2 * Real.pi * c * -(x * y) : ℝ) : ℂ) * Complex.I) =
      Complex.I * (-2 * Real.pi * c * x : ℂ) * y := by push_cast; ring
  simp_rw [hk]
  conv_lhs => enter [2, y]; rw [mul_comm]
  rw [fourierIntegral_gaussian (by simpa using hε), Gaussian.Construction.realDampedGaussian_eq c 1 ε hε]
  simp only [Complex.ofReal_one, mul_one]
  congr 1
  congr 1
  field_simp
  ring

theorem realQuadraticDamping_tendsto (c x : ℝ) :
    Tendsto (fun ε => realQuadraticDamping c ε x) (𝓝[>] (0 : ℝ))
      (𝓝 (Gaussian.Construction.realCharacter c (x ^ 2 / 2))) := by
  have h : ContinuousAt (fun ε : ℝ => realQuadraticDamping c ε x) 0 := by
    unfold realQuadraticDamping
    fun_prop
  simpa [realQuadraticDamping] using h.tendsto.mono_left nhdsWithin_le_nhds

theorem realQuadraticDamping_norm_le (c ε x : ℝ) (hε : 0 ≤ ε) :
    ‖realQuadraticDamping c ε x‖ ≤ 1 := by
  have hu : ‖Gaussian.Construction.realCharacter c (x ^ 2 / 2)‖ = 1 := Circle.norm_coe _
  rw [realQuadraticDamping, norm_mul, hu, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε) (sq_nonneg x))

theorem realFresnelGaussian_factor_norm_le (c ε x : ℝ) (hε : 0 ≤ ε) :
    ‖Complex.exp (-((Real.pi : ℂ) ^ 2 * c ^ 2 * x ^ 2) /
      ((ε : ℂ) - Real.pi * c * Complex.I))‖ ≤ 1 := by
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  have he : -((Real.pi : ℂ) ^ 2 * c ^ 2 * x ^ 2) = (-(Real.pi ^ 2 * c ^ 2 * x ^ 2) : ℝ) := by
    push_cast
    rfl
  rw [he]
  simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero,
    sub_zero, add_zero, zero_div]
  apply div_nonpos_of_nonpos_of_nonneg
  · nlinarith [sq_nonneg (Real.pi * c * x)]
  · exact Complex.normSq_nonneg _

theorem realDampedGaussian_tendsto (c : ℝ) (hc : c ≠ 0) :
    Tendsto (Gaussian.Construction.realDampedGaussian c 1) (𝓝[>] (0 : ℝ))
      (𝓝 ((Complex.I / (c : ℂ)) ^ (1 / 2 : ℂ))) := by
  have hr : (Gaussian.Construction.realReferenceHaarFactor : ℂ) ≠ 0 := by
    exact_mod_cast Gaussian.Construction.realReferenceHaarFactor_pos.ne'
  have h := (Gaussian.Construction.regularizedGaussian_real_tendsto c 1 hc one_ne_zero).const_mul
    (Gaussian.Construction.realReferenceHaarFactor : ℂ)⁻¹
  simp only [Complex.ofReal_one, mul_one, ← mul_assoc, inv_mul_cancel₀ hr, one_mul] at h
  apply h.congr
  intro ε
  rw [Gaussian.Construction.regularizedGaussian_real, ← mul_assoc, inv_mul_cancel₀ hr, one_mul]

theorem realFresnelGaussian_factor_tendsto (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    Tendsto (fun ε : ℝ => Complex.exp (-((Real.pi : ℂ) ^ 2 * c ^ 2 * x ^ 2) /
      ((ε : ℂ) - Real.pi * c * Complex.I))) (𝓝[>] (0 : ℝ))
      (𝓝 (Gaussian.Construction.realCharacter c (-(x ^ 2 / 2)))) := by
  have hden : ((0 : ℝ) : ℂ) - Real.pi * c * Complex.I ≠ 0 := by
    simp [hc, Real.pi_ne_zero]
  have ht : ContinuousAt (fun ε : ℝ => Complex.exp (-((Real.pi : ℂ) ^ 2 * c ^ 2 * x ^ 2) /
      ((ε : ℂ) - Real.pi * c * Complex.I))) 0 :=
    Complex.continuous_exp.continuousAt.comp
      (continuousAt_const.div (Complex.continuous_ofReal.continuousAt.sub continuousAt_const) hden)
  convert ht.tendsto.mono_left nhdsWithin_le_nhds using 1
  congr 1
  rw [Gaussian.Construction.realCharacter_apply]
  congr 1
  push_cast
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  linear_combination (Real.pi : ℂ) * c * x ^ 2 * Complex.I_sq

theorem scalarFourier_realQuadraticDamping_tendsto (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    Tendsto (fun ε => FourierTensor.Construction.scalarFourierIntegral (Gaussian.Construction.realCharacter c) volume
      (realQuadraticDamping c ε) x) (𝓝[>] (0 : ℝ))
      (𝓝 (((Complex.I / (c : ℂ)) ^ (1 / 2 : ℂ)) * Gaussian.Construction.realCharacter c (-(x ^ 2 / 2)))) := by
  apply ((realDampedGaussian_tendsto c hc).mul (realFresnelGaussian_factor_tendsto c hc x)).congr'
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with ε hε
  exact (scalarFourier_realQuadraticDamping c ε hε x).symm

end

/-! Scalar Gaussian Fourier limits with an arbitrary nonzero quadratic coefficient. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology

theorem scalarFourier_realCharacter_div (c a : ℝ) (ha : a ≠ 0) (f : ℝ → ℂ) (x : ℝ) :
    FourierTensor.Construction.scalarFourierIntegral (Gaussian.Construction.realCharacter c) volume f x =
      FourierTensor.Construction.scalarFourierIntegral (Gaussian.Construction.realCharacter (c * a)) volume f (x / a) := by
  unfold FourierTensor.Construction.scalarFourierIntegral
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [Gaussian.Construction.realCharacter_apply, Gaussian.Construction.realCharacter_apply]
    congr 3
    field_simp

theorem realCharacter_inverse_quadratic (c a x : ℝ) :
    Gaussian.Construction.realCharacter (c * a) (-((x / a) ^ 2 / 2)) = Gaussian.Construction.realCharacter c (-(a⁻¹ * x ^ 2 / 2)) := by
  rw [Gaussian.Construction.realCharacter_apply, Gaussian.Construction.realCharacter_apply]
  congr 2
  field_simp

theorem scalarFourier_realDiagonalGaussian_tendsto
    (c : ℝ) (hc : c ≠ 0) (a : ℝ) (ha : a ≠ 0) (x : ℝ) :
    Tendsto (fun ε => FourierTensor.Construction.scalarFourierIntegral (Gaussian.Construction.realCharacter c) volume
      (realQuadraticDamping (c * a) ε) x) (𝓝[>] (0 : ℝ))
      (𝓝 (((Complex.I / ((c * a : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
        Gaussian.Construction.realCharacter c (-(a⁻¹ * x ^ 2 / 2)))) := by
  simp_rw [scalarFourier_realCharacter_div c a ha]
  have h := scalarFourier_realQuadraticDamping_tendsto (c * a) (mul_ne_zero hc ha) (x / a)
  rwa [realCharacter_inverse_quadratic c a x] at h

theorem scalarFourier_realDiagonalGaussian_norm_le
    (c a : ℝ) (ha : a ≠ 0) (ε : ℝ) (hε : 0 < ε) (x : ℝ) :
    ‖FourierTensor.Construction.scalarFourierIntegral (Gaussian.Construction.realCharacter c) volume (realQuadraticDamping (c * a) ε) x‖ ≤
      ‖Gaussian.Construction.realDampedGaussian (c * a) 1 ε‖ := by
  rw [scalarFourier_realCharacter_div c a ha, scalarFourier_realQuadraticDamping (c * a) ε hε, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (realFresnelGaussian_factor_norm_le (c * a) ε (x / a) hε.le)

theorem realCharacter_quadratic_coefficient (c a x : ℝ) :
    Gaussian.Construction.realCharacter (c * a) (x ^ 2 / 2) = Gaussian.Construction.realCharacter c (a * x ^ 2 / 2) := by
  rw [Gaussian.Construction.realCharacter_apply, Gaussian.Construction.realCharacter_apply]
  congr 2
  push_cast
  ring

end

end OAI.RepresentationTheory.Weil.Local.RealDiagonalGaussian.Construction
