import OAI.Analysis.PDE.Dirichlet.Continuity
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

open Set Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

/-- Locally uniform convergence of the first two derivatives identifies both
derivative limits with the actual derivatives of the pointwise limit. -/
theorem second_fderiv_of_locally_uniform_limit
    {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {Ω : Set E} (hΩ : IsOpen Ω) {u : ℕ → E → Y} {v : E → Y}
    {G : E → E →L[ℝ] Y} {H : E → E →L[ℝ] E →L[ℝ] Y}
    (hu : ∀ k, ContDiff ℝ 2 (u k))
    (hv : ∀ x ∈ Ω, Tendsto (fun k ↦ u k x) atTop (𝓝 (v x)))
    (hG : TendstoLocallyUniformlyOn (fun k ↦ fderiv ℝ (u k)) G atTop Ω)
    (hH : TendstoLocallyUniformlyOn (fun k ↦ fderiv ℝ (fderiv ℝ (u k))) H atTop Ω) :
    ∀ x ∈ Ω, fderiv ℝ v x = G x ∧ fderiv ℝ (fderiv ℝ v) x = H x := by
  have hv' (x) (hx : x ∈ Ω) : HasFDerivAt v (G x) x :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn hΩ hG
      (fun k x _ ↦ ((hu k).differentiable (by norm_num) x).hasFDerivAt) hv hx
  have hG' (x) (hx : x ∈ Ω) : HasFDerivAt G (H x) x :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn hΩ hH
      (fun k x _ ↦ (((hu k).fderiv_right (m := 1) (by norm_num)).differentiable
        (by norm_num) x).hasFDerivAt) (fun x hx ↦ hG.tendsto_at hx) hx
  intro x hx
  refine ⟨(hv' x hx).fderiv, ?_⟩
  have he : fderiv ℝ v =ᶠ[𝓝 x] G :=
    Filter.eventually_of_mem (hΩ.mem_nhds hx) (fun y hy ↦ (hv' y hy).fderiv)
  exact he.fderiv_eq.trans (hG' x hx).fderiv

/-- The same limit is genuinely C² on the open domain. Continuity of the
second derivative is obtained from locally uniform convergence. -/
theorem contDiffOn_two_of_locally_uniform_derivatives
    {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {Ω : Set E} (hΩ : IsOpen Ω) {u : ℕ → E → Y} {v : E → Y}
    {G : E → E →L[ℝ] Y} {H : E → E →L[ℝ] E →L[ℝ] Y}
    (hu : ∀ k, ContDiff ℝ 2 (u k))
    (hv : ∀ x ∈ Ω, Tendsto (fun k ↦ u k x) atTop (𝓝 (v x)))
    (hG : TendstoLocallyUniformlyOn (fun k ↦ fderiv ℝ (u k)) G atTop Ω)
    (hH : TendstoLocallyUniformlyOn (fun k ↦ fderiv ℝ (fderiv ℝ (u k))) H atTop Ω) :
    ContDiffOn ℝ 2 v Ω := by
  have hv' (x) (hx : x ∈ Ω) : HasFDerivAt v (G x) x :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn hΩ hG
      (fun k x _ ↦ ((hu k).differentiable (by norm_num) x).hasFDerivAt) hv hx
  have hG' (x) (hx : x ∈ Ω) : HasFDerivAt G (H x) x :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn hΩ hH
      (fun k x _ ↦ (((hu k).fderiv_right (m := 1) (by norm_num)).differentiable
        (by norm_num) x).hasFDerivAt) (fun x hx ↦ hG.tendsto_at hx) hx
  have hHcont : ContinuousOn H Ω := hH.continuousOn (Frequently.of_forall (fun k ↦
    ((((hu k).fderiv_right (m := 1) (by norm_num)).fderiv_right
      (m := 0) (by norm_num)).continuous).continuousOn))
  have hGcont : ContDiffOn ℝ 1 G Ω := by
    change ContDiffOn ℝ (0 + 1) G Ω
    rw [contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨fun x hx ↦ (hG' x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact hHcont.congr (fun x hx ↦ (hG' x hx).fderiv)
  change ContDiffOn ℝ (1 + 1) v Ω
  rw [contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
  exact ⟨fun x hx ↦ (hv' x hx).differentiableAt.differentiableWithinAt, by simp,
    hGcont.congr (fun x hx ↦ (hv' x hx).fderiv)⟩

end OAI.Analysis.PDE.Dirichlet
