import OAI.Analysis.Fourier.SquareFunction.CombiningConstants
import OAI.Analysis.Fourier.BochnerRiesz.VectorDilation

open OAI.Analysis.Fourier.Wave

/-! Actual normalized kernel dilations and their differential estimates. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal

noncomputable def dilatedKernel {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    (K : Space n → H) (a : ℝ) (x : Space n) : H :=
  ((a ^ n : ℝ) : ℂ) • K (a • x)

theorem differentiable_dilatedKernel {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    {K : Space n → H} (hK : Differentiable ℝ K) (a : ℝ) :
    Differentiable ℝ (dilatedKernel K a) :=
  (hK.comp (differentiable_id.const_smul a)).const_smul ((a ^ n : ℝ) : ℂ)

theorem dilatedKernel_decay {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    {K : Space n → H} {a q C : ℝ} (ha : 0 < a)
    (hK : ∀ u, ‖K u‖ ≤ C * (‖u‖ + 1) ^ (-q)) (x : Space n) :
    ‖dilatedKernel K a x‖ ≤ C * a ^ n * (a * ‖x‖ + 1) ^ (-q) := by
  unfold dilatedKernel
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ha.le _)]
  have h := mul_le_mul_of_nonneg_left (hK (a • x)) (pow_nonneg ha.le n)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos ha, mul_left_comm, mul_assoc] using h

theorem dilatedKernel_derivative_decay {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H]
    {K : Space n → H} {a q C : ℝ} (ha : 0 < a)
    (hKd : Differentiable ℝ K)
    (hK : ∀ u, ‖fderiv ℝ K u‖ ≤ C * (‖u‖ + 1) ^ (-q)) (x : Space n) :
    ‖fderiv ℝ (dilatedKernel K a) x‖ ≤ C * (a ^ n * a) * (a * ‖x‖ + 1) ^ (-q) := by
  let A : Space n →L[ℝ] Space n := a • ContinuousLinearMap.id ℝ (Space n)
  have hA : ‖A‖ ≤ a := by
    apply ContinuousLinearMap.opNorm_le_bound _ ha.le
    intro u
    simp only [A, smul_apply, ContinuousLinearMap.id_apply,
      norm_smul, Real.norm_eq_abs, abs_of_pos ha, le_refl]
  have hd := ((hKd (a • x)).hasFDerivAt.comp x A.hasFDerivAt).const_smul ((a ^ n : ℝ) : ℂ)
  have hde : fderiv ℝ (dilatedKernel K a) x =
      ((a ^ n : ℝ) : ℂ) • ((fderiv ℝ K (a • x)).comp A) := hd.fderiv
  rw [hde, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg ha.le _)]
  calc
    _ ≤ a ^ n * (‖fderiv ℝ K (a • x)‖ * ‖A‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (pow_nonneg ha.le _)
    _ ≤ a ^ n * (‖fderiv ℝ K (a • x)‖ * a) := by gcongr
    _ ≤ a ^ n * ((C * (‖a • x‖ + 1) ^ (-q)) * a) := by gcongr; exact hK _
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]; ring

theorem convolve_dilatedKernel {n : ℕ} {H : Type*}
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (K : Space n → H) (f : Space n → ℂ) {a : ℝ} (ha : 0 < a) (x : Space n) :
    convolveKernel (dilatedKernel K a) f x =
      convolveKernel K (fun y => f (a⁻¹ • y)) (a • x) := by
  have hchange := Measure.integral_comp_smul_of_nonneg (volume : Measure (Space n))
    (fun y => f (a⁻¹ • y) • K (a • x - y)) a (hR := ha.le)
  simp only [Space, finrank_euclideanSpace_fin, inv_smul_smul₀ ha.ne'] at hchange
  have hscale : ((a ^ n : ℝ) : ℂ) •
      (∫ y, f y • K (a • x - a • y)) =
      ∫ y, f (a⁻¹ • y) • K (a • x - y) := by
    rw [hchange]
    change (a ^ n : ℝ) • ((a ^ n)⁻¹ • (∫ y, f (a⁻¹ • y) • K (a • x - y))) = _
    rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero n ha.ne'), one_smul]
  calc
    _ = ((a ^ n : ℝ) : ℂ) • (∫ y, f y • K (a • x - a • y)) := by
      rw [convolveKernel, ← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [dilatedKernel, smul_sub]
      exact smul_comm _ _ _
    _ = _ := hscale

end OAI.Analysis.Fourier.SquareFunction
