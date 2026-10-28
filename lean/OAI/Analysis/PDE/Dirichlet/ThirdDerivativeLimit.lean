import OAI.Analysis.PDE.Dirichlet.DerivativeLimit

open Set Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

/-- The third derivative of the actual value limit is identified by
locally uniform convergence of the full third-order jet. -/
theorem third_fderiv_of_locally_uniform_limit
    {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {Ω : Set E} (hΩ : IsOpen Ω) {u : ℕ → E → Y} {v : E → Y}
    {G : E → E →L[ℝ] Y} {H : E → E →L[ℝ] E →L[ℝ] Y}
    {T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] Y}
    (hu : ∀ k, ContDiff ℝ 3 (u k))
    (hv : ∀ x ∈ Ω, Tendsto (fun k => u k x) atTop (𝓝 (v x)))
    (hG : TendstoLocallyUniformlyOn (fun k => fderiv ℝ (u k)) G atTop Ω)
    (hH : TendstoLocallyUniformlyOn (fun k => fderiv ℝ (fderiv ℝ (u k))) H atTop Ω)
    (hT : TendstoLocallyUniformlyOn (fun k => fderiv ℝ (fderiv ℝ (fderiv ℝ (u k)))) T atTop Ω) :
    ∀ x ∈ Ω, fderiv ℝ (fderiv ℝ (fderiv ℝ v)) x = T x := by
  have htwo := second_fderiv_of_locally_uniform_limit hΩ
    (fun k => (hu k).of_le (by norm_num)) hv hG hH
  have hd (x) (hx : x ∈ Ω) : HasFDerivAt H (T x) x :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn hΩ hT
      (fun k x _ => ((((hu k).fderiv_right (m := 2) (by norm_num)).fderiv_right
        (m := 1) (by norm_num)).differentiable (by norm_num) x).hasFDerivAt)
      (fun x hx => hH.tendsto_at hx) hx
  intro x hx
  have he : fderiv ℝ (fderiv ℝ v) =ᶠ[𝓝 x] H :=
    Filter.eventually_of_mem (hΩ.mem_nhds hx) (fun y hy => (htwo y hy).2)
  exact he.fderiv_eq.trans (hd x hx).fderiv

theorem contDiffOn_three_of_locally_uniform_derivatives
    {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {Ω : Set E} (hΩ : IsOpen Ω) {u : ℕ → E → Y} {v : E → Y}
    {G : E → E →L[ℝ] Y} {H : E → E →L[ℝ] E →L[ℝ] Y}
    {T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] Y}
    (hu : ∀ k, ContDiff ℝ 3 (u k))
    (hv : ∀ x ∈ Ω, Tendsto (fun k => u k x) atTop (𝓝 (v x)))
    (hG : TendstoLocallyUniformlyOn (fun k => fderiv ℝ (u k)) G atTop Ω)
    (hH : TendstoLocallyUniformlyOn (fun k => fderiv ℝ (fderiv ℝ (u k))) H atTop Ω)
    (hT : TendstoLocallyUniformlyOn (fun k => fderiv ℝ (fderiv ℝ (fderiv ℝ (u k)))) T atTop Ω) :
    ContDiffOn ℝ 3 v Ω := by
  have hv' (x) (hx : x ∈ Ω) : HasFDerivAt v (G x) x :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn hΩ hG
      (fun k x _ => ((hu k).differentiable (by norm_num) x).hasFDerivAt) hv hx
  have hGtwo : ContDiffOn ℝ 2 G Ω :=
    contDiffOn_two_of_locally_uniform_derivatives hΩ
      (fun k => (hu k).fderiv_right (by norm_num)) (fun x hx => hG.tendsto_at hx) hH hT
  change ContDiffOn ℝ (2+1) v Ω
  rw [contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
  exact ⟨fun x hx => (hv' x hx).differentiableAt.differentiableWithinAt, by simp,
    hGtwo.congr (fun x hx => (hv' x hx).fderiv)⟩

end OAI.Analysis.PDE.Dirichlet
