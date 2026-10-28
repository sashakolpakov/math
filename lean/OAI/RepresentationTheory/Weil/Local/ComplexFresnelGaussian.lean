import OAI.RepresentationTheory.Weil.Local.RealDiagonalGaussian
import OAI.RepresentationTheory.Weil.Local.ComplexStandardNormalization

/-! # Complex Fresnel Gaussian -/

namespace OAI.RepresentationTheory.Weil.Local.ComplexFresnelGaussian.Construction

noncomputable section

/-! Complex Gaussian Fourier cutoffs, including cancellation of the two real phases. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology ComplexConjugate

def complexQuadraticDamping (ε : ℝ) (z : ℂ) : ℂ :=
  RealDiagonalGaussian.Construction.realQuadraticDamping 1 ε z.re * RealDiagonalGaussian.Construction.realQuadraticDamping (-1) ε z.im

theorem complexQuadraticDamping_continuous (ε : ℝ) : Continuous (complexQuadraticDamping ε) := by
  unfold complexQuadraticDamping
  simp_rw [RealDiagonalGaussian.Construction.realQuadraticDamping_eq]
  fun_prop

theorem complexQuadraticDamping_integrable (ε : ℝ) (hε : 0 < ε) :
    Integrable (complexQuadraticDamping ε) := by
  rw [← Complex.volume_preserving_equiv_real_prod.symm.integrable_comp_emb
    Complex.measurableEquivRealProd.symm.measurableEmbedding]
  exact (RealDiagonalGaussian.Construction.realQuadraticDamping_integrable 1 ε hε).mul_prod
    (RealDiagonalGaussian.Construction.realQuadraticDamping_integrable (-1) ε hε)

theorem complexStandardCharacter_quadratic (z : ℂ) :
    ArchimedeanTestSpace.Construction.complexStandardCharacter (z ^ 2 / 2) =
      Gaussian.Construction.realCharacter 1 (z.re ^ 2 / 2) * Gaussian.Construction.realCharacter (-1) (z.im ^ 2 / 2) := by
  change Gaussian.Construction.realCharacter 1 ((z ^ 2 / 2).re) = _
  rw [Gaussian.Construction.realCharacter_apply, Gaussian.Construction.realCharacter_apply, Gaussian.Construction.realCharacter_apply, ← Complex.exp_add]
  congr 1
  simp [pow_two]
  ring

theorem complexQuadraticDamping_tendsto (z : ℂ) :
    Tendsto (fun ε => complexQuadraticDamping ε z) (𝓝[>] (0 : ℝ))
      (𝓝 (ArchimedeanTestSpace.Construction.complexStandardCharacter (z ^ 2 / 2))) := by
  rw [complexStandardCharacter_quadratic]
  exact (RealDiagonalGaussian.Construction.realQuadraticDamping_tendsto 1 z.re).mul (RealDiagonalGaussian.Construction.realQuadraticDamping_tendsto (-1) z.im)

theorem complexQuadraticDamping_norm_le (ε : ℝ) (hε : 0 ≤ ε) (z : ℂ) :
    ‖complexQuadraticDamping ε z‖ ≤ 1 := by
  rw [complexQuadraticDamping, norm_mul]
  exact (mul_le_mul_of_nonneg_right
    (RealDiagonalGaussian.Construction.realQuadraticDamping_norm_le 1 ε z.re hε) (norm_nonneg _)).trans
      (by simpa only [one_mul] using RealDiagonalGaussian.Construction.realQuadraticDamping_norm_le (-1) ε z.im hε)

theorem scalarFourier_complexQuadraticDamping (ε : ℝ) (z : ℂ) :
    FourierTensor.Construction.scalarFourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume (complexQuadraticDamping ε) z =
      FourierTensor.Construction.scalarFourierIntegral (Gaussian.Construction.realCharacter 1) volume (RealDiagonalGaussian.Construction.realQuadraticDamping 1 ε) z.re *
        FourierTensor.Construction.scalarFourierIntegral (Gaussian.Construction.realCharacter (-1)) volume (RealDiagonalGaussian.Construction.realQuadraticDamping (-1) ε) z.im := by
  unfold FourierTensor.Construction.scalarFourierIntegral
  rw [← Complex.volume_preserving_equiv_real_prod.symm.integral_comp
    Complex.measurableEquivRealProd.symm.measurableEmbedding, ← integral_prod_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun p : ℝ × ℝ => by
    have hχ : ArchimedeanTestSpace.Construction.complexStandardCharacter (-(z * Complex.measurableEquivRealProd.symm p)) =
        Gaussian.Construction.realCharacter 1 (-(z.re * p.1)) * Gaussian.Construction.realCharacter (-1) (-(z.im * p.2)) := by
      change Gaussian.Construction.realCharacter 1 ((-(z * Complex.measurableEquivRealProd.symm p)).re) = _
      rw [Gaussian.Construction.realCharacter_apply, Gaussian.Construction.realCharacter_apply, Gaussian.Construction.realCharacter_apply, ← Complex.exp_add]
      congr 1
      simp only [Complex.neg_re, Complex.mul_re, Complex.measurableEquivRealProd_symm_apply, mul_one]
      push_cast
      ring
    dsimp only
    rw [hχ]
    change (RealDiagonalGaussian.Construction.realQuadraticDamping 1 ε p.1 * RealDiagonalGaussian.Construction.realQuadraticDamping (-1) ε p.2) * _ = _
    ring

theorem realDampedGaussian_opposite_product_tendsto :
    Tendsto (fun ε => Gaussian.Construction.realDampedGaussian 1 1 ε * Gaussian.Construction.realDampedGaussian (-1) 1 ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℂ)) := by
  have he (ε : ℝ) : Gaussian.Construction.realDampedGaussian (-1) 1 ε = conj (Gaussian.Construction.realDampedGaussian 1 1 ε) := by
    rw [ArchimedeanTestSpace.Construction.realDampedGaussian_conj]
    unfold Gaussian.Construction.realDampedGaussian
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [Gaussian.Construction.realCharacter_apply, Gaussian.Construction.realCharacter_apply]
      congr 2
      push_cast
      ring
  have hsq : (Complex.I ^ (1 / 2 : ℂ)) ^ (2 : ℕ) = Complex.I := by simp [one_div]
  have hn : ‖Complex.I ^ (1 / 2 : ℂ)‖ ^ 2 = 1 := by
    simpa only [norm_pow, Complex.norm_I] using congrArg norm hsq
  have hprod : Complex.I ^ (1 / 2 : ℂ) * conj (Complex.I ^ (1 / 2 : ℂ)) = 1 := by
    rw [Complex.mul_conj, ← Complex.sq_norm, hn]
    rfl
  simp_rw [he]
  simpa only [hprod, Function.comp_apply] using! ArchimedeanTestSpace.Construction.realDampedGaussian_standard_tendsto.mul
    ((Complex.continuous_conj.tendsto _).comp ArchimedeanTestSpace.Construction.realDampedGaussian_standard_tendsto)

theorem scalarFourier_complexQuadraticDamping_tendsto (z : ℂ) :
    Tendsto (fun ε => FourierTensor.Construction.scalarFourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume (complexQuadraticDamping ε) z)
      (𝓝[>] (0 : ℝ)) (𝓝 (ArchimedeanTestSpace.Construction.complexStandardCharacter (-(z ^ 2 / 2)))) := by
  have hphase : Gaussian.Construction.realCharacter 1 (-(z.re ^ 2 / 2)) * Gaussian.Construction.realCharacter (-1) (-(z.im ^ 2 / 2)) =
      ArchimedeanTestSpace.Construction.complexStandardCharacter (-(z ^ 2 / 2)) := by
    simp_rw [AddChar.map_neg_eq_inv]
    rw [complexStandardCharacter_quadratic, mul_inv]
  have h := realDampedGaussian_opposite_product_tendsto.mul
    ((RealDiagonalGaussian.Construction.realFresnelGaussian_factor_tendsto 1 one_ne_zero z.re).mul
      (RealDiagonalGaussian.Construction.realFresnelGaussian_factor_tendsto (-1) (by norm_num) z.im))
  simp only [one_mul, hphase] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with ε hε
  rw [scalarFourier_complexQuadraticDamping,
    RealDiagonalGaussian.Construction.scalarFourier_realQuadraticDamping 1 ε hε, RealDiagonalGaussian.Construction.scalarFourier_realQuadraticDamping (-1) ε hε]
  ring

theorem scalarFourier_complexQuadraticDamping_norm_le (ε : ℝ) (hε : 0 < ε) (z : ℂ) :
    ‖FourierTensor.Construction.scalarFourierIntegral ArchimedeanTestSpace.Construction.complexStandardCharacter volume (complexQuadraticDamping ε) z‖ ≤
      ‖Gaussian.Construction.realDampedGaussian 1 1 ε * Gaussian.Construction.realDampedGaussian (-1) 1 ε‖ := by
  rw [scalarFourier_complexQuadraticDamping,
    RealDiagonalGaussian.Construction.scalarFourier_realQuadraticDamping 1 ε hε, RealDiagonalGaussian.Construction.scalarFourier_realQuadraticDamping (-1) ε hε]
  simp only [norm_mul]
  calc
    _ = (‖Gaussian.Construction.realDampedGaussian 1 1 ε‖ * ‖Gaussian.Construction.realDampedGaussian (-1) 1 ε‖) *
        (‖Complex.exp (-((Real.pi : ℂ) ^ 2 * (1 : ℝ) ^ 2 * z.re ^ 2) /
          ((ε : ℂ) - Real.pi * (1 : ℝ) * Complex.I))‖ *
        ‖Complex.exp (-((Real.pi : ℂ) ^ 2 * (-1 : ℝ) ^ 2 * z.im ^ 2) /
          ((ε : ℂ) - Real.pi * (-1 : ℝ) * Complex.I))‖) := by ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity)
      ((mul_le_mul_of_nonneg_right
        (RealDiagonalGaussian.Construction.realFresnelGaussian_factor_norm_le 1 ε z.re hε.le) (norm_nonneg _)).trans
          (by simpa only [one_mul] using RealDiagonalGaussian.Construction.realFresnelGaussian_factor_norm_le (-1) ε z.im hε.le))

end

end OAI.RepresentationTheory.Weil.Local.ComplexFresnelGaussian.Construction
