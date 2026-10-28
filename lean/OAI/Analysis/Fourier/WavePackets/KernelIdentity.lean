import OAI.Analysis.Fourier.WavePackets.Poisson

namespace OAI.Analysis.Fourier.WavePackets

open _root_.MeasureTheory
open scoped ContDiff RealInnerProductSpace FourierTransform

noncomputable def waveAmplitude {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (h T : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) : ℂ :=
  Complex.exp (-Complex.I * (((T / h) * ‖ξ‖ : ℝ) : ℂ)) * φ ξ

theorem hasCompactSupport_waveAmplitude {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℂ}
    (hs : HasCompactSupport φ) (h T : ℝ) : HasCompactSupport (waveAmplitude φ h T) :=
  hs.mul_left

theorem contDiff_waveAmplitude {n : ℕ} {φ : EuclideanSpace ℝ (Fin n) → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ)
    (h T : ℝ) : ContDiff ℝ ∞ (waveAmplitude φ h T) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : ξ = 0
  · subst ξ
    have hz : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport (waveAmplitude φ h T) := by
      exact fun hz => hzero (tsupport_mul_subset_right hz)
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hz)
  · have hc := Complex.ofRealCLM.contDiff.contDiffAt.comp ξ
      ((contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : EuclideanSpace ℝ (Fin n) => T / h) ξ).mul
        (contDiffAt_norm ℝ hξ))
    exact (((contDiffAt_const.mul hc).cexp).mul hφ.contDiffAt)

/-- The Schwartz symbol expressed in the unit-torus dual coordinate. -/
noncomputable def periodicSchwartzSymbol {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hs : HasCompactSupport φ)
    (hφ : ContDiff ℝ ∞ φ) (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ)
    {h : ℝ} (hh : 0 < h) (T : ℝ) : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ :=
  ((hasCompactSupport_waveAmplitude hs h T).comp_smul
    (show h * (2 * Real.pi / 100) ≠ 0 by positivity)).toSchwartzMap
      ((contDiff_waveAmplitude hφ hzero h T).comp (by fun_prop))

theorem periodicSchwartzSymbol_apply {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hs : HasCompactSupport φ)
    (hφ : ContDiff ℝ ∞ φ) (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ)
    {h : ℝ} (hh : 0 < h) (T : ℝ) (ξ : EuclideanSpace ℝ (Fin n)) :
    periodicSchwartzSymbol hs hφ hzero hh T ξ =
      waveAmplitude φ h T ((h * (2 * Real.pi / 100)) • ξ) := rfl

theorem periodicSchwartzSymbol_integer {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hs : HasCompactSupport φ)
    (hφ : ContDiff ℝ ∞ φ) (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ)
    {h : ℝ} (hh : 0 < h) (T : ℝ) (k : Fin n → ℤ) :
    periodicSchwartzSymbol hs hφ hzero hh T (integerVector k) = periodicSymbol φ h T k := by
  rw [periodicSchwartzSymbol_apply]
  unfold waveAmplitude periodicSymbol periodicFrequency
  rw [← smul_smul]
  congr 2
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
  field_simp

/-- The exact Poisson identity for the cutoff wave symbol, with the physical
side-100 kernel normalization. -/
theorem periodicKernel_eq_inverseSymbol_sum {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hs : HasCompactSupport φ)
    (hφ : ContDiff ℝ ∞ φ) (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ)
    {h : ℝ} (hh : 0 < h) (T : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    periodicKernel φ h T (torusProjection x) =
      ∑' k : Fin n → ℤ, ((100 : ℂ) ^ n)⁻¹ *
        (𝓕⁻ (periodicSchwartzSymbol hs hφ hzero hh T)) (integerVector k + x) := by
  rw [tsum_mul_left, periodicKernel]
  congr 1
  rw [schwartz_poisson, FourierTransform.fourier_fourierInv_eq]
  apply tsum_congr
  intro k
  rw [periodicSchwartzSymbol_integer]

theorem waveFourier_integrand_identity {n : ℕ}
    (φ : EuclideanSpace ℝ (Fin n) → ℂ) {h : ℝ} (hh : h ≠ 0) (T : ℝ)
    (X ξ : EuclideanSpace ℝ (Fin n)) :
    Complex.exp (((2 * Real.pi * ⟪ξ, (1 / 100 : ℝ) • X⟫ : ℝ) : ℂ) * Complex.I) *
        waveAmplitude φ h T ((h * (2 * Real.pi / 100)) • ξ) =
      oscillation (euclideanWavePhase X T) h ((h * (2 * Real.pi / 100)) • ξ) *
        φ ((h * (2 * Real.pi / 100)) • ξ) := by
  unfold waveAmplitude oscillation euclideanWavePhase
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [inner_smul_right, real_inner_comm ξ X]
  push_cast
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  field_simp [hh']
  ring

/-- Conversion from the unit-torus Fourier inversion convention to the
semiclassical angular-frequency kernel, including its `(2π)⁻ⁿ` factor. -/
theorem inverseSymbol_eq_semiclassicalKernel {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hs : HasCompactSupport φ)
    (hφ : ContDiff ℝ ∞ φ) (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ)
    {h : ℝ} (hh : 0 < h) (T : ℝ) (X : EuclideanSpace ℝ (Fin n)) :
    ((100 : ℂ) ^ n)⁻¹ * (𝓕⁻ (periodicSchwartzSymbol hs hφ hzero hh T))
      ((1 / 100 : ℝ) • X) =
      (((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹ * semiclassicalWaveKernel volume φ h T X := by
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  simp only [smul_eq_mul, periodicSchwartzSymbol_apply]
  simp_rw [waveFourier_integrand_identity φ hh.ne' T X]
  rw [Measure.integral_comp_smul_of_nonneg volume
    (fun ξ => oscillation (euclideanWavePhase X T) h ξ * φ ξ)
    (h * (2 * Real.pi / 100)) (hR := by positivity)]
  simp only [semiclassicalWaveKernel, finrank_euclideanSpace, Fintype.card_fin,
    Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_ofNat]
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hh', hpi]
  have hfactor : (1 / 50 : ℂ) ^ n * (100 : ℂ) ^ n = (2 : ℂ) ^ n := by
    rw [← mul_pow]
    norm_num
  linear_combination -(∫ ξ, oscillation (euclideanWavePhase X T) h ξ * φ ξ) *
    (Real.pi : ℂ) ^ n * (h : ℂ) ^ n * hfactor

/-- The Fourier-series kernel on the side-100 torus is exactly the lattice
periodization of the Euclidean semiclassical kernel. -/
theorem periodicKernel_eq_lattice_sum {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hs : HasCompactSupport φ)
    (hφ : ContDiff ℝ ∞ φ) (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ)
    {h : ℝ} (hh : 0 < h) (T : ℝ) (X : EuclideanSpace ℝ (Fin n)) :
    periodicKernel φ h T (torusProjection ((1 / 100 : ℝ) • X)) =
      ∑' k : Fin n → ℤ, (((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹ *
        semiclassicalWaveKernel volume φ h T (X + (100 : ℝ) • integerVector k) := by
  rw [periodicKernel_eq_inverseSymbol_sum hs hφ hzero hh]
  apply tsum_congr
  intro k
  have hx : integerVector k + (1 / 100 : ℝ) • X =
      (1 / 100 : ℝ) • (X + (100 : ℝ) • integerVector k) := by module
  rw [hx, inverseSymbol_eq_semiclassicalKernel hs hφ hzero hh]

theorem periodicKernel_eq_kernel_add_remainder {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℂ} (hs : HasCompactSupport φ)
    (hφ : ContDiff ℝ ∞ φ) (hzero : (0 : EuclideanSpace ℝ (Fin n)) ∉ tsupport φ)
    {h : ℝ} (hh : 0 < h) (T : ℝ) (X : EuclideanSpace ℝ (Fin n)) :
    periodicKernel φ h T (torusProjection ((1 / 100 : ℝ) • X)) =
      (((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹ *
        (semiclassicalWaveKernel volume φ h T X + periodizationRemainder volume φ h T X) := by
  classical
  have hx (k : Fin n → ℤ) : integerVector k + (1 / 100 : ℝ) • X =
      (1 / 100 : ℝ) • (X + (100 : ℝ) • integerVector k) := by module
  have hsum : Summable (fun k : Fin n → ℤ => (((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹ *
      semiclassicalWaveKernel volume φ h T (X + (100 : ℝ) • integerVector k)) := by
    apply ((summable_norm_schwartz_lattice_add
      (𝓕⁻ (periodicSchwartzSymbol hs hφ hzero hh T)) ((1 / 100 : ℝ) • X)).of_norm.mul_left
        (((100 : ℂ) ^ n)⁻¹)).congr
    intro k
    rw [hx, inverseSymbol_eq_semiclassicalKernel hs hφ hzero hh]
  have hzeroEq : integerLatticeEquiv n 0 = 0 := by
    apply Subtype.ext
    ext i
    simp [integerLatticeEquiv, integerVector]
  have hz (k : Fin n → ℤ) : integerLatticeEquiv n k = 0 ↔ k = 0 := by
    rw [← hzeroEq]
    exact (integerLatticeEquiv n).injective.eq_iff
  have htail : (∑' k : Fin n → ℤ,
      if k = 0 then 0 else semiclassicalWaveKernel volume φ h T (X + (100 : ℝ) • integerVector k)) =
      periodizationRemainder volume φ h T X := by
    have he := (integerLatticeEquiv n).tsum_eq (periodizationRemainderTerm volume φ h T X)
    unfold periodizationRemainder
    convert he using 1
    congr 1
    funext k
    simp only [periodizationRemainderTerm, hz]
    rfl
  rw [periodicKernel_eq_lattice_sum hs hφ hzero hh, hsum.tsum_eq_add_tsum_ite 0]
  have hvec : integerVector (0 : Fin n → ℤ) = 0 := by ext i; simp [integerVector]
  simp only [hvec, smul_zero, add_zero]
  rw [mul_add]
  congr 1
  rw [← htail, ← tsum_mul_left]
  apply tsum_congr
  intro k
  split_ifs <;> simp

end OAI.Analysis.Fourier.WavePackets
