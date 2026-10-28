import OAI.Analysis.Fourier.SquareFunction.FourierDilation
import OAI.Analysis.Fourier.SquareFunction.Scaling

open OAI.Analysis.Fourier.Wave

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped Topology

namespace OAI.Analysis.Fourier.SquareFunction

theorem radius_derivative_integral_dilation {n : ℕ} (α : ℝ)
    (g : Space n → ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ ξ, (r⁻¹ * radiusMultiplier α ‖ξ‖ r) • g ξ) =
      (r^n * r⁻¹) • ∫ ξ, radiusMultiplier α ‖ξ‖ 1 • g (r • ξ) := by
  let F : Space n → ℂ := fun ξ => (r⁻¹ * radiusMultiplier α ‖ξ‖ r) • g ξ
  have hchange : (∫ ξ, F (r • ξ)) = (r^n)⁻¹ • ∫ ξ, F ξ := by
    simpa only [Space,finrank_euclideanSpace_fin] using
      Measure.integral_comp_smul_of_nonneg (volume : Measure (Space n)) F r (hR:=hr.le)
  have hkernel (ξ : Space n) : radiusMultiplier α ‖r • ξ‖ r =
      radiusMultiplier α ‖ξ‖ 1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr]
    simpa only [mul_one] using radiusMultiplier_scale hr α ‖ξ‖ 1
  calc
    (∫ ξ, F ξ) = r^n • ∫ ξ, F (r • ξ) := by
      rw [hchange,smul_smul,mul_inv_cancel₀ (pow_ne_zero n hr.ne'),one_smul]
    _ = r^n • (r⁻¹ • ∫ ξ, radiusMultiplier α ‖ξ‖ 1 • g (r • ξ)) := by
      congr 1
      simp only [F,hkernel,mul_smul,integral_smul]
    _ = _ := smul_smul _ _ _

theorem continuous_integral_fixed_weight_dilate {n : ℕ}
    {w : Space n → ℝ} (hw : Integrable w) {g : Space n → ℂ}
    (hg : Continuous g) {M : ℝ} (hM : ∀ ξ, ‖g ξ‖ ≤ M) :
    Continuous (fun r : ℝ => ∫ ξ, w ξ • g (r • ξ)) := by
  apply continuous_of_dominated
    (bound := fun ξ => ‖w ξ‖ * M)
  · intro r
    have hg' : Continuous (fun ξ : Space n => g (r • ξ)) := hg.comp (by fun_prop)
    exact hw.aestronglyMeasurable.smul hg'.aestronglyMeasurable
  · intro r
    filter_upwards [] with ξ
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
  · exact hw.norm.mul_const M
  · filter_upwards [] with ξ
    have hg' : Continuous (fun r : ℝ => g (r • ξ)) := hg.comp (by fun_prop)
    exact (continuous_const (y:=w ξ) : Continuous (fun _ : ℝ => w ξ)).smul hg'

theorem continuousOn_radius_derivative_integral_of_unit_integrable {n : ℕ}
    (α : ℝ) (hw : Integrable (fun ξ : Space n => radiusMultiplier α ‖ξ‖ 1))
    {g : Space n → ℂ} (hg : Continuous g) {M : ℝ} (hM : ∀ ξ, ‖g ξ‖ ≤ M) :
    ContinuousOn (fun r => ∫ ξ, (r⁻¹ * radiusMultiplier α ‖ξ‖ r) • g ξ) (Ioi 0) := by
  have hc := continuous_integral_fixed_weight_dilate hw hg hM
  have hf : ContinuousOn (fun r : ℝ => (r^n * r⁻¹) •
      ∫ ξ, radiusMultiplier α ‖ξ‖ 1 • g (r • ξ)) (Ioi 0) :=
    (continuousOn_id.pow n |>.mul (continuousOn_id.inv₀ fun r hr => ne_of_gt hr)).smul hc.continuousOn
  apply hf.congr
  intro r hr
  exact radius_derivative_integral_dilation α g hr

end OAI.Analysis.Fourier.SquareFunction
