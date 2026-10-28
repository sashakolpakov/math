import OAI.Analysis.PDE.Schauder.Calculus.Schauder.KernelScale

/-! Decay of the derivative of the actual Newtonian Hessian kernel. -/

noncomputable section
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem fderiv_smul_of_eventual_scaling (f : E → ℝ) (c a : ℝ) (x : E)
    (hc : c ≠ 0) (hf : DifferentiableAt ℝ f x)
    (hfc : DifferentiableAt ℝ f (c • x))
    (hh : ∀ᶠ y in 𝓝 x, f (c • y) = a * f y) :
    fderiv ℝ f (c • x) = (a / c) • fderiv ℝ f x := by
  have hl := hfc.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul c)
  have hr : HasFDerivAt (fun y => f (c • y)) (a • fderiv ℝ f x) x :=
    (hf.hasFDerivAt.const_mul a).congr_of_eventuallyEq hh
  have he := hl.unique hr
  ext v
  have hev := congrArg (fun L : E →L[ℝ] ℝ => L v) he
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    map_smul, smul_eq_mul] at hev
  change (fderiv ℝ f (c • x)) v = (a / c) * (fderiv ℝ f x) v
  apply (mul_left_cancel₀ hc)
  calc
    c * (fderiv ℝ f (c • x)) v = a * (fderiv ℝ f x) v := hev
    _ = c * ((a / c) * (fderiv ℝ f x) v) := by field_simp

theorem fderiv_newtonianEntry_smul (m : ℕ) (v w : E) {x : E} (hx : x ≠ 0)
    {c : ℝ} (hc : 0 < c) :
    fderiv ℝ (newtonianEntry m v w) (c • x) =
      c ^ (-(m : ℝ) - 1) • fderiv ℝ (newtonianEntry m v w) x := by
  have hh : ∀ᶠ y in 𝓝 x,
      newtonianEntry m v w (c • y) = c ^ (-(m : ℝ)) * newtonianEntry m v w y := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
    exact newtonianEntry_smul m v w hy hc
  have h := fderiv_smul_of_eventual_scaling (newtonianEntry m v w) c (c ^ (-(m : ℝ))) x
    hc.ne' ((contDiffAt_newtonianEntry m v w hx).differentiableAt (by norm_num))
    ((contDiffAt_newtonianEntry m v w (smul_ne_zero hc.ne' hx)).differentiableAt (by norm_num)) hh
  rwa [← Real.rpow_sub_one hc.ne'] at h

theorem newtonianEntry_fderiv_decay [FiniteDimensional ℝ E] (m : ℕ) (v w : E) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E, x ≠ 0 →
      ‖fderiv ℝ (newtonianEntry m v w) x‖ ≤ C * ‖x‖ ^ (-(m : ℝ) - 1) := by
  have hc : ContinuousOn (fun x => ‖fderiv ℝ (newtonianEntry m v w) x‖)
      (Metric.sphere (0 : E) 1) := by
    intro x hx
    have hx0 : x ≠ 0 := by intro he; simp [he] at hx
    exact ((contDiffAt_newtonianEntry m v w hx0).continuousAt_fderiv (by norm_num)).norm.continuousWithinAt
  obtain ⟨B, hB⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn hc
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro x hx
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let q := ‖x‖⁻¹ • x
  have hq : q ∈ Metric.sphere (0 : E) 1 := by
    simp [q, norm_smul, hn.ne']
  have hq0 : q ≠ 0 := by intro he; simp [he] at hq
  have hs := fderiv_newtonianEntry_smul m v w hq0 hn
  have he : ‖x‖ • q = x := smul_inv_smul₀ hn.ne' x
  rw [he] at hs
  have hb : ‖fderiv ℝ (newtonianEntry m v w) q‖ ≤ |B| + 1 := by
    have hb' := hB q hq
    simp only [Real.norm_eq_abs, abs_norm] at hb'
    exact hb'.trans (by linarith [le_abs_self B])
  rw [hs, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hn _)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hb
    (Real.rpow_nonneg hn.le (-(m : ℝ) - 1))

end OAI.Analysis.PDE.Schauder
