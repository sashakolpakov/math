import OAI.Analysis.Fourier.Restriction.Sparse.Kernel
import OAI.Analysis.Fourier.Restriction.SphereMass

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem localizedFourierKernel_eq_zero {n : ℕ} (u : SchwartzMap (Space n) ℂ)
    (hu : ∀ ξ, 1 / 8 ≤ ‖ξ‖ → OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ = 0)
    {R : ℝ} (hR : 0 < R) (z ω ξ : Space n) (h : R⁻¹ ≤ dist ω ξ) :
    localizedFourierKernel u R z ω ξ = 0 := by
  rw [localizedFourierKernel_eq u hR, hu, mul_zero]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR, ← dist_eq_norm]
  have H := mul_le_mul_of_nonneg_left h hR.le
  rw [mul_inv_cancel₀ hR.ne'] at H
  linarith

theorem enorm_localizedFourierKernel_le_indicator {n : ℕ} (u : SchwartzMap (Space n) ℂ)
    (hu : ∀ ξ, ‖OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ‖ ≤ 1)
    (hs : ∀ ξ, 1 / 8 ≤ ‖ξ‖ → OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ = 0)
    {R : ℝ} (hR : 0 < R) (z ω ξ : Space n) :
    ‖localizedFourierKernel u R z ω ξ‖ₑ ≤
      (ball ξ R⁻¹).indicator (fun _ ↦ ENNReal.ofReal (R ^ n)) ω := by
  by_cases h : ω ∈ ball ξ R⁻¹
  · rw [indicator_of_mem h, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    rw [norm_localizedFourierKernel u hR]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (hu (R • (ω - ξ))) (pow_nonneg hR.le n)
  · rw [indicator_of_notMem h, localizedFourierKernel_eq_zero u hs hR z ω ξ (by
      simpa only [mem_ball, not_lt] using h)]
    simp

theorem lintegral_localizedFourierKernel_le_ball {n : ℕ} (u : SchwartzMap (Space n) ℂ)
    (hu : ∀ ξ, ‖OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ‖ ≤ 1)
    (hs : ∀ ξ, 1 / 8 ≤ ‖ξ‖ → OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ = 0)
    (μ : Measure (Space n)) {R : ℝ} (hR : 0 < R) (z ξ : Space n) :
    (∫⁻ ω, ‖localizedFourierKernel u R z ω ξ‖ₑ ∂μ) ≤
      ENNReal.ofReal (R ^ n) * μ (ball ξ R⁻¹) := by
  calc
    _ ≤ ∫⁻ ω, (ball ξ R⁻¹).indicator (fun _ ↦ ENNReal.ofReal (R ^ n)) ω ∂μ :=
      lintegral_mono (enorm_localizedFourierKernel_le_indicator u hu hs hR z · ξ)
    _ = _ := by rw [lintegral_indicator measurableSet_ball]; simp

theorem localizedFourierKernel_column {n : ℕ} (hn : 1 ≤ n)
    (u : SchwartzMap (Space n) ℂ)
    (hu : ∀ ξ, ‖OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ‖ ≤ 1)
    (hs : ∀ ξ, 1 / 8 ≤ ‖ξ‖ → OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℝ, 0 < R → ∀ z ξ : Space n,
      (∫⁻ ω, ‖localizedFourierKernel u R z ω ξ‖ₑ ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) ≤
        ENNReal.ofReal (C * R) := by
  obtain ⟨C, hC, HC⟩ := sphere_ball_mass_upper hn
  refine ⟨C, hC, ?_⟩
  intro R hR z ξ
  have hp : R ^ n = R ^ (n - 1) * R := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have he : R ^ n * (C * (R⁻¹) ^ (n - 1)) = C * R := by
    rw [hp, inv_pow]
    field_simp
  calc
    _ ≤ ENNReal.ofReal (R ^ n) * OAI.Analysis.Fourier.Restriction.sphereMeasure n (ball ξ R⁻¹) :=
      lintegral_localizedFourierKernel_le_ball u hu hs _ hR z ξ
    _ ≤ ENNReal.ofReal (R ^ n) * ENNReal.ofReal (C * (R⁻¹) ^ (n - 1)) :=
      mul_le_mul' le_rfl (HC R⁻¹ (inv_pos.mpr hR) ξ)
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity), he]

theorem localizedFourierKernel_row {n : ℕ} (u : SchwartzMap (Space n) ℂ)
    (hu : ∀ ξ, ‖OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ‖ ≤ 1)
    (hs : ∀ ξ, 1 / 8 ≤ ‖ξ‖ → OAI.Analysis.Fourier.LocalSmoothing.angularFourier u ξ = 0)
    {R : ℝ} (hR : 0 < R) (z ω : Space n) :
    (∫⁻ ξ, ‖localizedFourierKernel u R z ω ξ‖ₑ) ≤ volume (ball (0 : Space n) 1) := by
  have hpoint (ξ : Space n) : ‖localizedFourierKernel u R z ω ξ‖ₑ ≤
      (ball ω R⁻¹).indicator (fun _ ↦ ENNReal.ofReal (R ^ n)) ξ := by
    have H := enorm_localizedFourierKernel_le_indicator u hu hs hR z ω ξ
    by_cases h : ξ ∈ ball ω R⁻¹
    · have h' : ω ∈ ball ξ R⁻¹ := by simpa only [mem_ball, dist_comm] using h
      simpa only [indicator_of_mem h, indicator_of_mem h'] using H
    · have h' : ω ∉ ball ξ R⁻¹ := by simpa only [mem_ball, dist_comm] using h
      simpa only [indicator_of_notMem h, indicator_of_notMem h'] using H
  calc
    _ ≤ ∫⁻ ξ, (ball ω R⁻¹).indicator (fun _ ↦ ENNReal.ofReal (R ^ n)) ξ := lintegral_mono hpoint
    _ = ENNReal.ofReal (R ^ n) * volume (ball ω R⁻¹) := by
      rw [lintegral_indicator measurableSet_ball]; simp
    _ = volume (ball (0 : Space n) 1) := by
      rw [Measure.addHaar_ball_of_pos volume _ (inv_pos.mpr hR)]
      simp only [Space, finrank_euclideanSpace_fin]
      rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hR.le n), ← mul_pow,
        mul_inv_cancel₀ hR.ne', one_pow, ENNReal.ofReal_one, one_mul]

end OAI.Analysis.Fourier.Restriction
