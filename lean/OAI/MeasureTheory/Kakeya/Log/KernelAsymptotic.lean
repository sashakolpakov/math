import OAI.MeasureTheory.Kakeya.Log.Kernel
import OAI.MeasureTheory.Kakeya.Log.Profile

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ContDiff RealInnerProductSpace

noncomputable section
namespace OAI.MeasureTheory.Kakeya

/-- Extend the sphere asymptotic to every positive radius by enlarging its
constant on the unit ball. This avoids a scale-dependent lower cutoff. -/
theorem normalizedSphere_asymptotic_all {n : ℕ} (hn : 1 ≤ n) :
    ∃ A B C : ℝ, 0 ≤ C ∧ 0 < A ^ 2 + B ^ 2 ∧ ∀ x : Space n, 0 < ‖x‖ →
      ‖OAI.Analysis.Fourier.LocalSmoothing.Sharpness.normalizedSphere n x - (OAI.Analysis.Fourier.Restriction.radialOscillation A B ‖x‖ : ℝ)‖ ≤
        C / ‖x‖ := by
  obtain ⟨A, B, C, hC, hAB, hAs⟩ := OAI.Analysis.Fourier.Radial.sphericalExtension_one_asymptotic hn
  let M : ℝ := ∫ z : Space n, ‖(1 : ℂ)‖ ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n
  have hM : 0 ≤ M := integral_nonneg (fun _ ↦ norm_nonneg _)
  have hβ : 0 ≤ OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialOrder n := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    dsimp [OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialOrder]
    linarith
  refine ⟨A, B, C + M + (|A| + |B|), by positivity, hAB, ?_⟩
  intro x hx
  by_cases hx1 : 1 ≤ ‖x‖
  · exact (hAs x hx1).trans (div_le_div_of_nonneg_right
      (by linarith [abs_nonneg A, abs_nonneg B]) hx.le)
  · have hxle : ‖x‖ ≤ 1 := (lt_of_not_ge hx1).le
    have hpow : ‖x‖ ^ OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialOrder n ≤ 1 :=
      Real.rpow_le_one (norm_nonneg _) hxle hβ
    have hnorm : ‖OAI.Analysis.Fourier.LocalSmoothing.Sharpness.normalizedSphere n x‖ ≤ M := by
      change ‖((‖x‖ ^ OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialOrder n : ℝ) : ℂ) *
        OAI.Analysis.Fourier.Restriction.sphericalExtension (fun _ : Space n ↦ (1 : ℂ)) x‖ ≤ M
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      calc
        _ ≤ 1 * M := mul_le_mul hpow (OAI.Analysis.Fourier.Restriction.norm_sphericalExtension_le _ x)
          (norm_nonneg _) (by positivity)
        _ = M := one_mul _
    have hosc : ‖(OAI.Analysis.Fourier.Restriction.radialOscillation A B ‖x‖ : ℝ)‖ ≤ |A| + |B| := by
      simpa only [Real.norm_eq_abs] using OAI.Analysis.Fourier.Restriction.abs_radialOscillation_le A B ‖x‖
    calc
      _ ≤ ‖OAI.Analysis.Fourier.LocalSmoothing.Sharpness.normalizedSphere n x‖ + ‖((OAI.Analysis.Fourier.Restriction.radialOscillation A B ‖x‖ : ℝ) : ℂ)‖ :=
        norm_sub_le _ _
      _ ≤ M + (|A| + |B|) := by
        simpa only [Complex.norm_real] using add_le_add hnorm hosc
      _ ≤ C + M + (|A| + |B|) := by linarith
      _ ≤ _ := (le_div_iff₀ hx).mpr (mul_le_of_le_one_right (by positivity) hxle)

theorem normalized_narrowKernel {n : ℕ} (hn : 1 ≤ n) {φ : ℝ → ℝ}
    (hφc : ContDiff ℝ ∞ φ) (hφ : tsupport φ ⊆ Icc (-(1 / 4)) (1 / 4))
    {T : ℝ} (hT : 1 ≤ T) {x : Space n} (hx : 0 < ‖x‖) :
    ((‖x‖ ^ OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialOrder n : ℝ) : ℂ) * narrowKernel n φ T x =
      (((2 * Real.pi) ^ n)⁻¹ : ℝ) •
        OAI.Analysis.Fourier.LocalSmoothing.Sharpness.normalizedRadialWave n (narrowProfile φ T) 0 x := by
  rw [narrowKernel_polar hn hφc hφ hT]
  simp only [OAI.Analysis.Fourier.LocalSmoothing.Sharpness.normalizedRadialWave, OAI.Analysis.Fourier.LocalSmoothing.Sharpness.phase, neg_zero, zero_mul,
    Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul]
  rw [mul_smul_comm, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ρ
  by_cases he : narrowProfile φ T ρ = 0
  · simp [he]
  · have hρ : 0 < ρ := by
      have := (narrowProfile_support hφ hT (subset_tsupport _ he)).1
      linarith
    have hr : ‖ρ • x‖ ^ OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialOrder n =
        ρ ^ OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialOrder n * ‖x‖ ^ OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialOrder n := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ,
        Real.mul_rpow hρ.le hx.le]
    simp only [OAI.Analysis.Fourier.LocalSmoothing.Sharpness.normalizedSphere, hr, Complex.ofReal_mul]
    ring

theorem narrowProfile_change_variables {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : ℝ → E) {T : ℝ} (hT : 0 < T) :
    (∫ ρ, F ρ) = T⁻¹ • ∫ u, F (1 + u / T) := by
  rw [← integral_add_left_eq_self F 1]
  rw [OAI.Analysis.Fourier.Radial.integral_rescale_real _ (inv_pos.mpr hT)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  congr 1
  ring

theorem integral_norm_narrowProfile (φ : ℝ → ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ ρ, ‖narrowProfile φ T ρ‖) = T⁻¹ * ∫ u, ‖φ u‖ := by
  rw [narrowProfile_change_variables _ hT, smul_eq_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  congr 2
  dsimp [narrowProfile]
  congr 1
  field_simp
  ring

theorem radialProfile_narrowProfile (φ : ℝ → ℝ) {T : ℝ} (hT : 0 < T) (r : ℝ) :
    OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialProfile (narrowProfile φ T) r =
      (T⁻¹ : ℝ) • (OAI.Analysis.Fourier.LocalSmoothing.Sharpness.phase r * OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialProfile φ (r / T)) := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialProfile
  rw [narrowProfile_change_variables _ hT, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  have he : narrowProfile φ T (1 + u / T) = φ u := by
    dsimp [narrowProfile]
    congr 1
    field_simp
    ring
  rw [he]
  change OAI.Analysis.Fourier.LocalSmoothing.Sharpness.phase (r * (1 + u / T)) * (φ u : ℂ) =
    OAI.Analysis.Fourier.LocalSmoothing.Sharpness.phase r * (OAI.Analysis.Fourier.LocalSmoothing.Sharpness.phase (r / T * u) * (φ u : ℂ))
  rw [← mul_assoc, OAI.Analysis.Fourier.LocalSmoothing.Sharpness.phase_mul]
  congr 2
  ring

/-- The full radial error is controlled uniformly in the shell thickness. -/
theorem narrow_radialWave_error {n : ℕ} {A B C : ℝ} (hn : 1 ≤ n) (hC : 0 ≤ C)
    (hAs : ∀ x : Space n, 0 < ‖x‖ →
      ‖OAI.Analysis.Fourier.LocalSmoothing.Sharpness.normalizedSphere n x - (OAI.Analysis.Fourier.Restriction.radialOscillation A B ‖x‖ : ℝ)‖ ≤ C / ‖x‖)
    {φ : ℝ → ℝ} (hφc : Continuous φ)
    (hφ : tsupport φ ⊆ Icc (-(1 / 4)) (1 / 4)) {T : ℝ} (hT : 1 ≤ T)
    {x : Space n} (hx : 0 < ‖x‖) :
    ‖OAI.Analysis.Fourier.LocalSmoothing.Sharpness.normalizedRadialWave n (narrowProfile φ T) 0 x -
      (OAI.Analysis.Fourier.LocalSmoothing.Sharpness.outgoingCoefficient A B * OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialProfile (narrowProfile φ T) ‖x‖ +
        star (OAI.Analysis.Fourier.LocalSmoothing.Sharpness.outgoingCoefficient A B) *
          OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialProfile (narrowProfile φ T) (-‖x‖))‖ ≤
      (2 * C / ‖x‖) * (T⁻¹ * ∫ u, ‖φ u‖) := by
  have hpc : Continuous (narrowProfile φ T) := by unfold narrowProfile; fun_prop
  have H := OAI.Analysis.Fourier.LocalSmoothing.Sharpness.integral_two_phase_error hpc (narrowProfile_hasCompactSupport hφ hT)
    ((OAI.Analysis.Fourier.LocalSmoothing.Sharpness.continuous_normalizedSphere hn).comp
      (by fun_prop : Continuous (fun ρ : ℝ ↦ ρ • x)))
    (OAI.Analysis.Fourier.LocalSmoothing.Sharpness.outgoingCoefficient A B) ‖x‖ 0 (2 * C / ‖x‖) (by positivity) ?_
  · simpa only [sub_zero, add_zero, OAI.Analysis.Fourier.LocalSmoothing.Sharpness.normalizedRadialWave, Function.comp_def,
      integral_norm_narrowProfile φ (by linarith : 0 < T)] using H
  · intro ρ hρ
    have hρlow := (narrowProfile_support hφ hT hρ).1
    have hρpos : 0 < ρ := by linarith
    have hr : ‖ρ • x‖ = ‖x‖ * ρ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρpos, mul_comm]
    have H := hAs (ρ • x) (by rw [hr]; positivity)
    have he : ((OAI.Analysis.Fourier.Restriction.radialOscillation A B (‖x‖ * ρ) : ℝ) : ℂ) =
        OAI.Analysis.Fourier.LocalSmoothing.Sharpness.outgoingCoefficient A B * OAI.Analysis.Fourier.LocalSmoothing.Sharpness.phase (‖x‖ * ρ) +
          star (OAI.Analysis.Fourier.LocalSmoothing.Sharpness.outgoingCoefficient A B) * OAI.Analysis.Fourier.LocalSmoothing.Sharpness.phase (-‖x‖ * ρ) := by
      rw [OAI.Analysis.Fourier.Restriction.radialOscillation, OAI.Analysis.Fourier.LocalSmoothing.Sharpness.two_phase_identity]
      simp only [OAI.Analysis.Fourier.LocalSmoothing.Sharpness.phase, Complex.ofReal_neg, neg_mul, mul_neg]
    rw [hr, he] at H
    apply H.trans
    apply (div_le_iff₀ (mul_pos hx hρpos)).mpr
    field_simp
    nlinarith

theorem kakeyaLogBump_narrow_support :
    tsupport (kakeyaLogBump : ℝ → ℝ) ⊆ Icc (-(1 / 4)) (1 / 4) := by
  apply closure_minimal ?_ isClosed_Icc
  intro u hu
  have h := abs_lt.mp (kakeyaLogBump_support hu)
  constructor <;> linarith [h.1, h.2]

theorem kakeyaCosineProfile_neg (s : ℝ) : kakeyaCosineProfile (-s) = kakeyaCosineProfile s := by
  simp only [kakeyaCosineProfile, neg_mul, Real.cos_neg]

theorem narrowRadial_mainTerm (A B r : ℝ) {T : ℝ} (hT : 0 < T) :
    (T : ℂ) *
      (OAI.Analysis.Fourier.LocalSmoothing.Sharpness.outgoingCoefficient A B *
          OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialProfile (narrowProfile (kakeyaLogBump : ℝ → ℝ) T) r +
        star (OAI.Analysis.Fourier.LocalSmoothing.Sharpness.outgoingCoefficient A B) *
          OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialProfile (narrowProfile (kakeyaLogBump : ℝ → ℝ) T) (-r)) =
      (kakeyaCosineProfile (r / T) : ℂ) * (OAI.Analysis.Fourier.Restriction.radialOscillation A B r : ℝ) := by
  rw [radialProfile_narrowProfile _ hT, radialProfile_narrowProfile _ hT,
    radialProfile_kakeyaLogBump, radialProfile_kakeyaLogBump,
    neg_div, kakeyaCosineProfile_neg, OAI.Analysis.Fourier.Restriction.radialOscillation, OAI.Analysis.Fourier.LocalSmoothing.Sharpness.two_phase_identity]
  have hTc : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  simp only [Complex.real_smul, Complex.ofReal_inv, OAI.Analysis.Fourier.LocalSmoothing.Sharpness.phase, Complex.ofReal_neg,
    mul_neg, neg_mul]
  field_simp

/-- Uniform leading oscillation of the actual thin-shell inverse Fourier
kernel. Neither the error constant nor the coefficients depend on thickness. -/
theorem kakeya_narrowKernel_asymptotic {n : ℕ} (hn : 1 ≤ n) :
    ∃ A B C : ℝ, 0 ≤ C ∧ 0 < A ^ 2 + B ^ 2 ∧ ∀ T : ℝ, 1 ≤ T →
      ∀ x : Space n, 0 < ‖x‖ →
      ‖((T * ‖x‖ ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) *
          narrowKernel n (kakeyaLogBump : ℝ → ℝ) T x -
        (kakeyaLogWeight n T ‖x‖ : ℂ) * (OAI.Analysis.Fourier.Restriction.radialOscillation A B ‖x‖ : ℝ)‖ ≤ C / ‖x‖ := by
  obtain ⟨A, B, C, hC, hAB, hAs⟩ := normalizedSphere_asymptotic_all hn
  let N : ℝ := ((2 * Real.pi) ^ n)⁻¹
  let M : ℝ := ∫ u, ‖kakeyaLogBump u‖
  have hN : 0 < N := by dsimp [N]; positivity
  have hM : 0 ≤ M := integral_nonneg (fun _ ↦ norm_nonneg _)
  refine ⟨A, B, N * (2 * C * M), by positivity, hAB, ?_⟩
  intro T hT x hx
  have hT0 : 0 < T := by linarith
  let W := OAI.Analysis.Fourier.LocalSmoothing.Sharpness.normalizedRadialWave n (narrowProfile (kakeyaLogBump : ℝ → ℝ) T) 0 x
  let Q := OAI.Analysis.Fourier.LocalSmoothing.Sharpness.outgoingCoefficient A B *
      OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialProfile (narrowProfile (kakeyaLogBump : ℝ → ℝ) T) ‖x‖ +
    star (OAI.Analysis.Fourier.LocalSmoothing.Sharpness.outgoingCoefficient A B) *
      OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialProfile (narrowProfile (kakeyaLogBump : ℝ → ℝ) T) (-‖x‖)
  have hmain : (T : ℂ) * Q =
      (kakeyaCosineProfile (‖x‖ / T) : ℂ) * (OAI.Analysis.Fourier.Restriction.radialOscillation A B ‖x‖ : ℝ) :=
    narrowRadial_mainTerm A B ‖x‖ hT0
  have hnorm : ((‖x‖ ^ OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialOrder n : ℝ) : ℂ) *
      narrowKernel n (kakeyaLogBump : ℝ → ℝ) T x = (N : ℝ) • W :=
    normalized_narrowKernel hn kakeyaLogBump.contDiff kakeyaLogBump_narrow_support hT hx
  have he : ((T * ‖x‖ ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) *
        narrowKernel n (kakeyaLogBump : ℝ → ℝ) T x -
      (kakeyaLogWeight n T ‖x‖ : ℂ) * (OAI.Analysis.Fourier.Restriction.radialOscillation A B ‖x‖ : ℝ) =
      ((N * T : ℝ) : ℂ) * (W - Q) := by
    change ((T * ‖x‖ ^ OAI.Analysis.Fourier.LocalSmoothing.Sharpness.radialOrder n : ℝ) : ℂ) * _ - _ = _
    rw [Complex.ofReal_mul, mul_assoc, hnorm]
    change (T : ℂ) * ((N : ℂ) * W) -
      ((N * kakeyaCosineProfile (‖x‖ / T) : ℝ) : ℂ) * _ = _
    rw [Complex.ofReal_mul, mul_assoc, ← hmain, Complex.ofReal_mul]
    ring
  have herror : ‖W - Q‖ ≤ (2 * C / ‖x‖) * (T⁻¹ * M) :=
    narrow_radialWave_error hn hC hAs kakeyaLogBump.continuous
      kakeyaLogBump_narrow_support hT hx
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos hN hT0)]
  calc
    _ ≤ N * T * ((2 * C / ‖x‖) * (T⁻¹ * M)) :=
      mul_le_mul_of_nonneg_left herror (mul_nonneg hN.le hT0.le)
    _ = N * (2 * C * M) / ‖x‖ := by field_simp

end OAI.MeasureTheory.Kakeya
