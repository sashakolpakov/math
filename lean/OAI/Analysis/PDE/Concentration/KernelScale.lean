import OAI.Analysis.PDE.Concentration.Smoothing

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current

theorem kernelProfile_enlarged_scale {d : ℕ} {c : ℝ} (hc : 1 ≤ c) (x : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    OAI.Analysis.Calculus.Current.kernelProfile d (c⁻¹ • x) ≤ c ^ (2 * (d + 3)) * OAI.Analysis.Calculus.Current.kernelProfile d x := by
  have hcpos : 0 < c := by linarith
  have hn : ‖x‖ = c * ‖c⁻¹ • x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcpos)]
    field_simp
  have hs : 1 + ‖x‖ ^ 2 ≤ c ^ 2 * (1 + ‖c⁻¹ • x‖ ^ 2) := by
    rw [hn]
    nlinarith [sq_nonneg (c - 1)]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖x‖ ^ 2) hs (d + 3)
  rw [mul_pow, ← pow_mul] at hp
  rw [kernelProfile_eq_inv_pow, kernelProfile_eq_inv_pow,
    ← one_div, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  simpa only [one_mul] using hp

/-- Replacing `h` by a fixed larger scale only changes the normalized
Japanese-bracket kernel by a dimension-dependent constant. -/
theorem smoothingKernel_enlarged_scale {d : ℕ} {c h : ℝ} (hc : 1 ≤ c) (hh : 0 < h)
    (x : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    OAI.Analysis.Calculus.Current.smoothingKernel d (c * h) x ≤ c ^ (2 * (d + 3)) * OAI.Analysis.Calculus.Current.smoothingKernel d h x := by
  have hcpos : 0 < c := by linarith
  have hcInv : (c ^ (d + 1))⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ (one_le_pow₀ hc)
  have hp := kernelProfile_enlarged_scale hc (h⁻¹ • x)
  have hnorm : (c * h)⁻¹ • x = c⁻¹ • (h⁻¹ • x) := by
    rw [smul_smul, mul_inv_rev, mul_comm]
  unfold OAI.Analysis.Calculus.Current.smoothingKernel
  rw [mul_pow, mul_inv_rev, hnorm]
  have hK : 0 ≤ OAI.Analysis.Calculus.Current.kernelConstant d := (OAI.Analysis.Calculus.Current.kernelConstant_pos d).le
  calc
    _ ≤ OAI.Analysis.Calculus.Current.kernelConstant d * (h ^ (d + 1))⁻¹ * OAI.Analysis.Calculus.Current.kernelProfile d (c⁻¹ • (h⁻¹ • x)) := by
      have hz : 0 ≤ OAI.Analysis.Calculus.Current.kernelProfile d (c⁻¹ • (h⁻¹ • x)) := (OAI.Analysis.Calculus.Current.kernelProfile_pos d _).le
      nlinarith [mul_le_mul_of_nonneg_left hcInv
        (show 0 ≤ OAI.Analysis.Calculus.Current.kernelConstant d * (h ^ (d + 1))⁻¹ * OAI.Analysis.Calculus.Current.kernelProfile d (c⁻¹ • (h⁻¹ • x)) by positivity)]
    _ ≤ OAI.Analysis.Calculus.Current.kernelConstant d * (h ^ (d + 1))⁻¹ * (c ^ (2 * (d + 3)) * OAI.Analysis.Calculus.Current.kernelProfile d (h⁻¹ • x)) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

theorem smoothingKernel_two_pi {d : ℕ} {h : ℝ} (hh : 0 < h) (x : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    OAI.Analysis.Calculus.Current.smoothingKernel d (2 * Real.pi * h) x ≤
      (2 * Real.pi) ^ (2 * (d + 3)) * OAI.Analysis.Calculus.Current.smoothingKernel d h x :=
  smoothingKernel_enlarged_scale (by linarith [Real.pi_gt_three]) hh x

end OAI.Analysis.PDE.Concentration
