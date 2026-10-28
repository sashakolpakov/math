import OAI.Analysis.PDE.Concentration.Kernel
import OAI.Analysis.Calculus.Current.Kernel

namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory OAI.Analysis.Calculus.Current Set
open scoped ContDiff

theorem kernelProfile_eq_inv_pow (d : ℕ) (x : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    OAI.Analysis.Calculus.Current.kernelProfile d x = ((1 + ‖x‖ ^ 2) ^ (d + 3))⁻¹ := by
  unfold OAI.Analysis.Calculus.Current.kernelProfile
  have he : -(2 * ((d : ℝ) + 1) + 4) / 2 = -((d + 3 : ℕ) : ℝ) := by push_cast; ring
  rw [he, Real.rpow_neg (by positivity), Real.rpow_natCast]

/-- The fixed `M = 2n+4` differentiability estimate controls the actual,
normalized smoothing kernel of the paper. -/
theorem finite_order_kernel_le_smoothing {d : ℕ} {S : Set (OAI.Analysis.Calculus.Current.SpatialSpace d)}
    (hS : IsCompact S) {b : OAI.Analysis.Calculus.Current.SpatialSpace d → ℂ}
    (hb : ContDiff ℝ (2 * (d + 3) : ℕ) b) (hs : tsupport b ⊆ S)
    {B : ℝ} (hB : 0 ≤ B)
    (hderiv : ∀ j ≤ 2 * (d + 3), ∀ x, ‖iteratedFDeriv ℝ j b x‖ ≤ B)
    {h : ℝ} (hh : 0 < h) (x : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    ‖scaledInverseKernel b h x‖ ≤
      ((2 ^ (2 * (d + 3)) * (1 + 2 ^ (2 * (d + 3)) * (2 * (d + 3) + 1)) *
        volume.real S) / OAI.Analysis.Calculus.Current.kernelConstant d) * B * OAI.Analysis.Calculus.Current.smoothingKernel d h x := by
  have hbound := finite_order_scaled_kernel_bracket hS hb hs hB hderiv hh x
  have he : (1 + ‖h⁻¹ • x‖ ^ 2) ^ (-((d + 3 : ℕ) : ℝ)) =
      OAI.Analysis.Calculus.Current.kernelProfile d (h⁻¹ • x) := by
    rw [kernelProfile_eq_inv_pow, Real.rpow_neg (by positivity), Real.rpow_natCast]
  rw [he] at hbound
  simp only [OAI.Analysis.Calculus.Current.SpatialSpace, finrank_euclideanSpace, Fintype.card_option, Fintype.card_fin] at hbound
  convert hbound using 1
  unfold OAI.Analysis.Calculus.Current.smoothingKernel
  field_simp [ne_of_gt (OAI.Analysis.Calculus.Current.kernelConstant_pos d)]
  push_cast
  ring

theorem one_add_norm_sq_le_of_dist_le_one {E : Type*} [SeminormedAddCommGroup E]
    {x y : E} (hxy : ‖x - y‖ ≤ 1) :
    1 + ‖x‖ ^ 2 ≤ 3 * (1 + ‖y‖ ^ 2) := by
  have hn : ‖x‖ ≤ ‖y‖ + 1 := by
    have ht := norm_add_le (x - y) y
    simpa only [sub_add_cancel] using ht.trans (by linarith)
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  nlinarith [sq_nonneg (‖y‖ - 1)]

theorem kernelProfile_comparable {d : ℕ} {x y : OAI.Analysis.Calculus.Current.SpatialSpace d}
    (hxy : ‖x - y‖ ≤ 1) :
    OAI.Analysis.Calculus.Current.kernelProfile d x ≤ 3 ^ (d + 3) * OAI.Analysis.Calculus.Current.kernelProfile d y := by
  rw [kernelProfile_eq_inv_pow, kernelProfile_eq_inv_pow]
  have h := one_add_norm_sq_le_of_dist_le_one
    (x := y) (y := x) (by simpa only [norm_sub_rev] using hxy)
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖y‖ ^ 2) h (d + 3)
  rw [mul_pow] at hp
  rw [← one_div, ← div_eq_mul_inv]
  exact (div_le_div_iff₀ (by positivity) (by positivity)).2 (by simpa using hp)

/-- Nearby spatial centers have comparable smoothing densities, uniformly
in the semiclassical scale. -/
theorem smoothingKernel_comparable {d : ℕ} {h : ℝ} (hh : 0 < h)
    {x y : OAI.Analysis.Calculus.Current.SpatialSpace d} (hxy : ‖x - y‖ ≤ h) :
    OAI.Analysis.Calculus.Current.smoothingKernel d h x ≤ 3 ^ (d + 3) * OAI.Analysis.Calculus.Current.smoothingKernel d h y := by
  have hscaled : ‖h⁻¹ • x - h⁻¹ • y‖ ≤ 1 := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
    exact (inv_mul_le_iff₀ hh).2 (by simpa using hxy)
  have hp := mul_le_mul_of_nonneg_left (kernelProfile_comparable hscaled)
    (mul_nonneg (OAI.Analysis.Calculus.Current.kernelConstant_pos d).le (inv_nonneg.mpr (pow_nonneg hh.le (d + 1))))
  simpa only [OAI.Analysis.Calculus.Current.smoothingKernel, mul_assoc, mul_left_comm, mul_comm] using hp

/-- Cauchy--Schwarz against a nonnegative mass-one density, proved by its
variance identity so that no square-root measurability interface is needed. -/
theorem weighted_integral_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {J f : α → ℝ} (hJ : ∀ x, 0 ≤ J x) (hiJ : Integrable J μ)
    (hmass : ∫ x, J x ∂μ = 1)
    (hif : Integrable (fun x => J x * f x) μ)
    (hif2 : Integrable (fun x => J x * (f x) ^ 2) μ) :
    (∫ x, J x * f x ∂μ) ^ 2 ≤ ∫ x, J x * (f x) ^ 2 ∂μ := by
  let m := ∫ x, J x * f x ∂μ
  have he (x : α) : J x * (f x - m) ^ 2 =
      J x * (f x) ^ 2 - (2 * m) * (J x * f x) + m ^ 2 * J x := by ring
  have hn : 0 ≤ ∫ x, J x * (f x - m) ^ 2 ∂μ :=
    integral_nonneg fun x => mul_nonneg (hJ x) (sq_nonneg _)
  simp_rw [he] at hn
  have hadd := integral_add (hif2.sub (hif.const_mul (2 * m))) (hiJ.const_mul (m ^ 2))
  have hsub := integral_sub hif2 (hif.const_mul (2 * m))
  simp only [Pi.sub_apply] at hadd hsub
  rw [hadd, hsub, integral_const_mul, integral_const_mul, hmass] at hn
  change m ^ 2 ≤ _
  change 0 ≤ (∫ x, J x * f x ^ 2 ∂μ) - (2 * m) * m + m ^ 2 * 1 at hn
  nlinarith

/-- The paper's pointwise recovery estimate for a kernel dominated by `C J`.
The input hypotheses are exactly the integrability needed for the two
weighted moments. -/
theorem pointwise_recovery_of_probability_majorant {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {J : α → ℝ} {k f : α → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hJ : ∀ x, 0 ≤ J x) (hiJ : Integrable J μ)
    (hmass : ∫ x, J x ∂μ = 1)
    (hif : Integrable (fun x => J x * ‖f x‖) μ)
    (hif2 : Integrable (fun x => J x * ‖f x‖ ^ 2) μ)
    (hk : ∀ x, ‖k x‖ ≤ C * J x) :
    ‖∫ x, k x * f x ∂μ‖ ≤ C * Real.sqrt (∫ x, J x * ‖f x‖ ^ 2 ∂μ) := by
  have hnorm : (∫ x, ‖k x * f x‖ ∂μ) ≤ C * ∫ x, J x * ‖f x‖ ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
      (hif.const_mul C)
    exact Filter.Eventually.of_forall fun x => by
      change ‖k x * f x‖ ≤ C * (J x * ‖f x‖)
      rw [norm_mul]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hk x) (norm_nonneg (f x))
  have hs := weighted_integral_sq_le hJ hiJ hmass hif hif2
  have hfirst : 0 ≤ ∫ x, J x * ‖f x‖ ∂μ := integral_nonneg fun x => mul_nonneg (hJ x) (norm_nonneg _)
  have hsecond : 0 ≤ ∫ x, J x * ‖f x‖ ^ 2 ∂μ := integral_nonneg fun x => mul_nonneg (hJ x) (sq_nonneg _)
  exact (norm_integral_le_integral_norm _).trans (hnorm.trans
    (mul_le_mul_of_nonneg_left ((Real.le_sqrt hfirst hsecond).2 hs) hC))

end OAI.Analysis.PDE.Concentration
