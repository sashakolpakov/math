import OAI.Analysis.PDE.Dirichlet.DensityPath

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

theorem norm_fderiv_log_le_of_bounds {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} {x : E} (hF : DifferentiableAt ℝ F x)
    {m L : ℝ} (hm : 0 < m) (hL : 0 ≤ L) (hmin : m ≤ F x)
    (hD : ‖fderiv ℝ F x‖ ≤ L) :
    ‖fderiv ℝ (fun y ↦ Real.log (F y)) x‖ ≤ L / m := by
  have hp : 0 < F x := hm.trans_le hmin
  rw [(hF.hasFDerivAt.log hp.ne').fderiv, norm_smul]
  calc
    ‖(F x)⁻¹‖ * ‖fderiv ℝ F x‖ = ‖fderiv ℝ F x‖ / F x := by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), div_eq_mul_inv, mul_comm]
    _ ≤ L / F x := div_le_div_of_nonneg_right hD hp.le
    _ ≤ L / m := div_le_div_of_nonneg_left hL hm hmin

end OAI.Analysis.PDE.Dirichlet
