import OAI.RepresentationTheory.Weil.UnitarySplitting.ArchimedeanGaussian

/-! # Complex Gaussian Fourier -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.ComplexGaussianFourier.Construction

noncomputable section

section

/-! Damped complex norm Gaussians with linear Fourier terms. -/

open _root_.MeasureTheory
open scoped InnerProductSpace

def complexDampedNormGaussian (t ε : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-((ε : ℂ) - Complex.I * t) * (Complex.normSq z : ℂ))

def complexDampedNormTransform (t ε : ℝ) (w : ℂ) : ℂ :=
  (Real.pi : ℂ) / ((ε : ℂ) - Complex.I * t) *
    Complex.exp (-((t ^ 2 * Complex.normSq w : ℝ) : ℂ) / ((ε : ℂ) - Complex.I * t))

theorem complex_damped_norm_fourier (t ε : ℝ) (hε : 0 < ε) (w : ℂ) :
    (∫ z : ℂ, complexDampedNormGaussian t ε z *
      Complex.exp (2 * Complex.I * t * (⟪w, z⟫_ℝ : ℂ))) = complexDampedNormTransform t ε w := by
  let b : ℂ := (ε : ℂ) - Complex.I * t
  have hb : 0 < b.re := by simpa [b] using hε
  have hb0 : b ≠ 0 := by
    intro hz
    rw [hz, Complex.zero_re] at hb
    exact lt_irrefl 0 hb
  have heq (z : ℂ) : complexDampedNormGaussian t ε z *
      Complex.exp (2 * Complex.I * t * (⟪w, z⟫_ℝ : ℂ)) =
        Complex.exp (-b * (‖z‖ : ℂ) ^ 2 + (2 * Complex.I * t) * (⟪w, z⟫_ℝ : ℂ)) := by
    rw [complexDampedNormGaussian, ← Complex.exp_add, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  simp_rw [heq]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb (2 * Complex.I * t) w]
  norm_num only [Complex.finrank_real_complex, Nat.cast_ofNat, div_self (by norm_num : (2 : ℂ) ≠ 0), Complex.cpow_one]
  change (Real.pi : ℂ) / b * Complex.exp ((2 * Complex.I * t) ^ 2 * (‖w‖ : ℂ) ^ 2 / (4 * b)) = _
  unfold complexDampedNormTransform
  congr 2
  rw [Complex.normSq_eq_norm_sq, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow]
  have hnum : (2 * Complex.I * (t : ℂ)) ^ 2 * (‖w‖ : ℂ) ^ 2 =
      -4 * ((t : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2) := by
    calc
      _ = 4 * Complex.I ^ 2 * ((t : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2) := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [hnum]
  change -4 * ((t : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2) / (4 * b) = -((t : ℂ) ^ 2 * (‖w‖ : ℂ) ^ 2) / b
  field_simp [hb0]

theorem complex_damped_norm_fourier_integrable (t ε : ℝ) (hε : 0 < ε) (w : ℂ) :
    Integrable (fun z : ℂ => complexDampedNormGaussian t ε z *
      Complex.exp (2 * Complex.I * t * (⟪w, z⟫_ℝ : ℂ))) := by
  have hb : 0 < ((ε : ℂ) - Complex.I * t).re := by simpa using hε
  have hi := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add hb (2 * Complex.I * t) w
  convert hi using 1
  funext z
  rw [complexDampedNormGaussian, ← Complex.exp_add, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

theorem complexDampedNormGaussian_norm_le_one (t ε : ℝ) (hε : 0 ≤ ε) (z : ℂ) :
    ‖complexDampedNormGaussian t ε z‖ ≤ 1 := by
  rw [complexDampedNormGaussian, Complex.norm_exp, Real.exp_le_one_iff]
  simp only [Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε) (Complex.normSq_nonneg z)

theorem complexDampedNormTransform_norm_le (t ε : ℝ) (ht : t ≠ 0) (hε : 0 ≤ ε) (w : ℂ) :
    ‖complexDampedNormTransform t ε w‖ ≤ Real.pi / |t| := by
  let b : ℂ := (ε : ℂ) - Complex.I * t
  have hre : (-((t ^ 2 * Complex.normSq w : ℝ) : ℂ) / b).re ≤ 0 := by
    rw [Complex.div_re]
    simp only [Complex.neg_re, Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, neg_zero,
      zero_mul, zero_div, add_zero]
    have hbr : 0 ≤ b.re := by simpa [b] using hε
    exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (mul_nonneg (sq_nonneg t) (Complex.normSq_nonneg w))) hbr)
      (Complex.normSq_nonneg b)
  have hb : |t| ≤ ‖b‖ := by
    have hh := Complex.abs_im_le_norm b
    simpa [b] using hh
  have hexp : ‖Complex.exp (-((t ^ 2 * Complex.normSq w : ℝ) : ℂ) / b)‖ ≤ 1 := by
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    exact hre
  change ‖(Real.pi : ℂ) / b * Complex.exp _‖ ≤ _
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    _ ≤ (Real.pi / ‖b‖) * 1 := mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = Real.pi / ‖b‖ := mul_one _
    _ ≤ Real.pi / |t| := div_le_div_of_nonneg_left Real.pi_pos.le (abs_pos.mpr ht) hb

end

section

/-! Boundary values of damped complex Gaussian Fourier kernels. -/

open Filter _root_.Topology

def complexNormGaussianValue (t : ℝ) : ℂ := (Real.pi : ℂ) / (-Complex.I * t)

theorem complexNormGaussianValue_ne_zero (t : ℝ) (ht : t ≠ 0) : complexNormGaussianValue t ≠ 0 :=
  div_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr ht))

theorem complexDampedNormGaussian_tendsto (t : ℝ) (z : ℂ) :
    Tendsto (fun ε : ℝ => complexDampedNormGaussian t ε z) (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.exp (Complex.I * t * (Complex.normSq z : ℂ)))) := by
  have hc : Continuous (fun ε : ℝ => complexDampedNormGaussian t ε z) := by
    unfold complexDampedNormGaussian
    fun_prop
  simpa only [complexDampedNormGaussian, Complex.ofReal_zero, zero_sub, neg_neg, neg_mul] using
    (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))

theorem complexDampedNormTransform_zero (t : ℝ) (ht : t ≠ 0) (w : ℂ) :
    complexDampedNormTransform t 0 w =
      complexNormGaussianValue t * Complex.exp (-Complex.I * t * (Complex.normSq w : ℂ)) := by
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  have hb : -Complex.I * (t : ℂ) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) htC
  unfold complexDampedNormTransform complexNormGaussianValue
  rw [Complex.ofReal_zero, zero_sub]
  simp only [← neg_mul]
  change (Real.pi : ℂ) / (-Complex.I * t) * Complex.exp _ = _
  congr 2
  rw [Complex.ofReal_mul, Complex.ofReal_pow]
  apply (div_eq_iff hb).mpr
  calc
    -((t : ℂ) ^ 2 * (Complex.normSq w : ℂ)) = Complex.I ^ 2 * (t : ℂ) ^ 2 * (Complex.normSq w : ℂ) := by
      rw [Complex.I_sq]
      ring
    _ = (-Complex.I * t * (Complex.normSq w : ℂ)) * (-Complex.I * t) := by ring

theorem complexDampedNormTransform_tendsto (t : ℝ) (ht : t ≠ 0) (w : ℂ) :
    Tendsto (fun ε : ℝ => complexDampedNormTransform t ε w) (𝓝[>] (0 : ℝ))
      (𝓝 (complexNormGaussianValue t * Complex.exp (-Complex.I * t * (Complex.normSq w : ℂ)))) := by
  have hb : (0 : ℂ) - Complex.I * (t : ℂ) ≠ 0 := by
    rw [zero_sub]
    exact neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr ht))
  have hden : ContinuousAt (fun ε : ℝ => (ε : ℂ) - Complex.I * t) 0 :=
    Complex.continuous_ofReal.continuousAt.sub continuousAt_const
  have hc : ContinuousAt (fun ε : ℝ => complexDampedNormTransform t ε w) 0 :=
    (continuousAt_const.div hden hb).mul
      (Complex.continuous_exp.continuousAt.comp (continuousAt_const.div hden hb))
  have hh := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  rwa [complexDampedNormTransform_zero t ht w] at hh

theorem complexNormBilinearPhase_norm (t : ℝ) (w z : ℂ) :
    ‖Complex.exp (2 * Complex.I * t * (inner ℝ w z : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  norm_num [Complex.mul_re, Complex.mul_im]

end

section

/-! Absolutely convergent Gaussian Fourier pairings before removing damping. -/

open _root_.MeasureTheory
open scoped InnerProductSpace

def complexNormFourierIntegral (t : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∫ w : ℂ, Complex.exp (2 * Complex.I * t * (inner ℝ w z : ℂ)) * f w

theorem complexDampedNormGaussian_continuous (t ε : ℝ) : Continuous (complexDampedNormGaussian t ε) := by
  unfold complexDampedNormGaussian
  fun_prop

theorem complexDampedNormTransform_continuous (t ε : ℝ) : Continuous (complexDampedNormTransform t ε) := by
  unfold complexDampedNormTransform
  fun_prop

theorem complexDampedNormGaussian_integrable (t ε : ℝ) (hε : 0 < ε) :
    Integrable (complexDampedNormGaussian t ε) := by
  have hh := complex_damped_norm_fourier_integrable t ε hε 0
  simpa only [inner_zero_left, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] using hh

theorem complexDampedNorm_pairing_integrable (t ε : ℝ) (hε : 0 < ε)
    (f : ℂ → ℂ) (hfc : Continuous f) (hfi : Integrable f) :
    Integrable (fun p : ℂ × ℂ => complexDampedNormGaussian t ε p.1 *
      (Complex.exp (2 * Complex.I * t * (inner ℝ p.2 p.1 : ℂ)) * f p.2))
        ((volume : Measure ℂ).prod volume) := by
  have hgc := complexDampedNormGaussian_continuous t ε
  have hgi := complexDampedNormGaussian_integrable t ε hε
  have hkc : Continuous (fun p : ℂ × ℂ => complexDampedNormGaussian t ε p.1 *
      (Complex.exp (2 * Complex.I * t * (inner ℝ p.2 p.1 : ℂ)) * f p.2)) := by fun_prop
  apply (hgi.norm.mul_prod hfi.norm).mono' hkc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun p => by
    change ‖complexDampedNormGaussian t ε p.1 *
      (Complex.exp (2 * Complex.I * t * (inner ℝ p.2 p.1 : ℂ)) * f p.2)‖ ≤
        ‖complexDampedNormGaussian t ε p.1‖ * ‖f p.2‖
    rw [norm_mul, norm_mul, complexNormBilinearPhase_norm, one_mul]

theorem complexDampedNorm_pairing (t ε : ℝ) (hε : 0 < ε)
    (f : ℂ → ℂ) (hfc : Continuous f) (hfi : Integrable f) :
    (∫ z : ℂ, complexDampedNormGaussian t ε z * complexNormFourierIntegral t f z) =
      ∫ w : ℂ, complexDampedNormTransform t ε w * f w := by
  calc
    _ = ∫ z : ℂ, ∫ w : ℂ, complexDampedNormGaussian t ε z *
        (Complex.exp (2 * Complex.I * t * (inner ℝ w z : ℂ)) * f w) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        dsimp only [complexNormFourierIntegral]
        rw [integral_const_mul]
    _ = ∫ w : ℂ, ∫ z : ℂ, complexDampedNormGaussian t ε z *
        (Complex.exp (2 * Complex.I * t * (inner ℝ w z : ℂ)) * f w) :=
      integral_integral_swap (complexDampedNorm_pairing_integrable t ε hε f hfc hfi)
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w => by
        simp only [← mul_assoc]
        rw [integral_mul_const, complex_damped_norm_fourier t ε hε w]

end

section

/-! The complex norm Gaussian Fourier law follows by dominated convergence. -/

open _root_.MeasureTheory Filter _root_.Topology

theorem complex_norm_gaussian_fourier_pairing (t : ℝ) (ht : t ≠ 0)
    (f : ℂ → ℂ) (hfc : Continuous f) (hfi : Integrable f)
    (hTc : Continuous (complexNormFourierIntegral t f)) (hTi : Integrable (complexNormFourierIntegral t f)) :
    (∫ z : ℂ, Complex.exp (Complex.I * t * (Complex.normSq z : ℂ)) * complexNormFourierIntegral t f z) =
      complexNormGaussianValue t * ∫ w : ℂ, Complex.exp (-Complex.I * t * (Complex.normSq w : ℂ)) * f w := by
  have hL : Tendsto (fun ε : ℝ => ∫ z : ℂ, complexDampedNormGaussian t ε z * complexNormFourierIntegral t f z)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ z : ℂ, Complex.exp (Complex.I * t * (Complex.normSq z : ℂ)) * complexNormFourierIntegral t f z)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun z => ‖complexNormFourierIntegral t f z‖)
    · exact Filter.Eventually.of_forall fun ε => ((complexDampedNormGaussian_continuous t ε).mul hTc).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Filter.Eventually.of_forall fun z => by
        change ‖complexDampedNormGaussian t ε z * complexNormFourierIntegral t f z‖ ≤ ‖complexNormFourierIntegral t f z‖
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (complexDampedNormGaussian_norm_le_one t ε hε.le z)
    · exact hTi.norm
    · exact Filter.Eventually.of_forall fun z => (complexDampedNormGaussian_tendsto t z).mul tendsto_const_nhds
  have hR : Tendsto (fun ε : ℝ => ∫ w : ℂ, complexDampedNormTransform t ε w * f w)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ w : ℂ, (complexNormGaussianValue t * Complex.exp (-Complex.I * t * (Complex.normSq w : ℂ))) * f w)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun w => (Real.pi / |t|) * ‖f w‖)
    · exact Filter.Eventually.of_forall fun ε => ((complexDampedNormTransform_continuous t ε).mul hfc).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Filter.Eventually.of_forall fun w => by
        change ‖complexDampedNormTransform t ε w * f w‖ ≤ (Real.pi / |t|) * ‖f w‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (complexDampedNormTransform_norm_le t ε ht hε.le w) (norm_nonneg _)
    · exact hfi.norm.const_mul _
    · exact Filter.Eventually.of_forall fun w => (complexDampedNormTransform_tendsto t ht w).mul tendsto_const_nhds
  have heq : (fun ε : ℝ => ∫ z : ℂ, complexDampedNormGaussian t ε z * complexNormFourierIntegral t f z) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε : ℝ => ∫ w : ℂ, complexDampedNormTransform t ε w * f w) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact complexDampedNorm_pairing t ε hε f hfc hfi
  have hh := tendsto_nhds_unique hL (hR.congr' heq.symm)
  rw [hh]
  simp only [mul_assoc]
  exact integral_const_mul _ _

end

/-! A convergent Gaussian regularization supplies an exact Fourier pairing law. -/

open _root_.MeasureTheory Filter _root_.Topology

structure GaussianFourierRegularization
    {V : Type} [TopologicalSpace V] [MeasurableSpace V]
    (μ : Measure V) (phase dual : V → ℂ) (kernel : V → V → ℂ) (Γ : ℂ) where
  gaussian : ℝ → V → ℂ
  transform : ℝ → V → ℂ
  bound : ℝ
  bound_pos : 0 < bound
  kernel_continuous : Continuous (fun p : V × V => kernel p.1 p.2)
  kernel_norm : ∀ v w, ‖kernel v w‖ = 1
  gaussian_continuous : ∀ ε, Continuous (gaussian ε)
  gaussian_integrable : ∀ ε, 0 < ε → Integrable (gaussian ε) μ
  gaussian_norm : ∀ ε, 0 < ε → ∀ v, ‖gaussian ε v‖ ≤ 1
  gaussian_limit : ∀ v, Tendsto (fun ε => gaussian ε v) (𝓝[>] (0 : ℝ)) (𝓝 (phase v))
  transform_continuous : ∀ ε, Continuous (transform ε)
  transform_bound : ∀ ε, 0 < ε → ∀ w, ‖transform ε w‖ ≤ bound
  transform_limit : ∀ w, Tendsto (fun ε => transform ε w) (𝓝[>] (0 : ℝ)) (𝓝 (Γ * dual w))
  integral_transform : ∀ ε, 0 < ε → ∀ w, (∫ v, gaussian ε v * kernel v w ∂μ) = transform ε w

namespace GaussianFourierRegularization

variable {V : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
variable {μ : Measure V} [SigmaFinite μ] {phase dual : V → ℂ} {kernel : V → V → ℂ} {Γ : ℂ}
variable (R : GaussianFourierRegularization μ phase dual kernel Γ)

theorem damped_pairing (ε : ℝ) (hε : 0 < ε) (f : V → ℂ) (hfc : Continuous f) (hfi : Integrable f μ) :
    (∫ v, R.gaussian ε v * (∫ w, kernel v w * f w ∂μ) ∂μ) =
      ∫ w, R.transform ε w * f w ∂μ := by
  have hkc : Continuous (fun p : V × V => R.gaussian ε p.1 * (kernel p.1 p.2 * f p.2)) :=
    ((R.gaussian_continuous ε).comp continuous_fst).mul
      (R.kernel_continuous.mul (hfc.comp continuous_snd))
  have hki : Integrable (fun p : V × V => R.gaussian ε p.1 * (kernel p.1 p.2 * f p.2)) (μ.prod μ) := by
    apply ((R.gaussian_integrable ε hε).norm.mul_prod hfi.norm).mono' hkc.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun p => by
      change ‖R.gaussian ε p.1 * (kernel p.1 p.2 * f p.2)‖ ≤ ‖R.gaussian ε p.1‖ * ‖f p.2‖
      rw [norm_mul, norm_mul, R.kernel_norm, one_mul]
  calc
    _ = ∫ v, ∫ w, R.gaussian ε v * (kernel v w * f w) ∂μ ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v => (integral_const_mul _ _).symm
    _ = ∫ w, ∫ v, R.gaussian ε v * (kernel v w * f w) ∂μ ∂μ := integral_integral_swap hki
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun w => by
        simp only [← mul_assoc]
        rw [integral_mul_const, R.integral_transform ε hε w]

include R in
theorem pairing (f : V → ℂ) (hfc : Continuous f) (hfi : Integrable f μ)
    (hTc : Continuous (fun v => ∫ w, kernel v w * f w ∂μ))
    (hTi : Integrable (fun v => ∫ w, kernel v w * f w ∂μ) μ) :
    (∫ v, phase v * (∫ w, kernel v w * f w ∂μ) ∂μ) = Γ * ∫ w, dual w * f w ∂μ := by
  let T : V → ℂ := fun v => ∫ w, kernel v w * f w ∂μ
  have hL : Tendsto (fun ε : ℝ => ∫ v, R.gaussian ε v * T v ∂μ) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ v, phase v * T v ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun v => ‖T v‖)
    · exact Filter.Eventually.of_forall fun ε => ((R.gaussian_continuous ε).mul hTc).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Filter.Eventually.of_forall fun v => by
        change ‖R.gaussian ε v * T v‖ ≤ ‖T v‖
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (R.gaussian_norm ε hε v)
    · exact hTi.norm
    · exact Filter.Eventually.of_forall fun v => (R.gaussian_limit v).mul tendsto_const_nhds
  have hR : Tendsto (fun ε : ℝ => ∫ w, R.transform ε w * f w ∂μ) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ w, (Γ * dual w) * f w ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun w => R.bound * ‖f w‖)
    · exact Filter.Eventually.of_forall fun ε => ((R.transform_continuous ε).mul hfc).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Filter.Eventually.of_forall fun w => by
        change ‖R.transform ε w * f w‖ ≤ R.bound * ‖f w‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (R.transform_bound ε hε w) (norm_nonneg _)
    · exact hfi.norm.const_mul _
    · exact Filter.Eventually.of_forall fun w => (R.transform_limit w).mul tendsto_const_nhds
  have heq : (fun ε : ℝ => ∫ v, R.gaussian ε v * T v ∂μ) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε : ℝ => ∫ w, R.transform ε w * f w ∂μ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact R.damped_pairing ε hε f hfc hfi
  rw [tendsto_nhds_unique hL (hR.congr' heq.symm)]
  simp only [mul_assoc]
  exact integral_const_mul _ _

end GaussianFourierRegularization

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.ComplexGaussianFourier.Construction
