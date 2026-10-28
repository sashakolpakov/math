import OAI.Analysis.PDE.Dirichlet.ThirdDerivativeLimit

open Set Filter
open scoped Topology
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
local instance fourthLimitFirstGroup : NormedAddCommGroup (E →L[ℝ] Y) := inferInstance
local instance fourthLimitFirstSpace : NormedSpace ℝ (E →L[ℝ] Y) := inferInstance
local instance fourthLimitSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] Y) := inferInstance
local instance fourthLimitSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] Y) := inferInstance
local instance fourthLimitThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] Y) := inferInstance
local instance fourthLimitThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] Y) := inferInstance
local instance fourthLimitFourthGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] Y) := inferInstance
local instance fourthLimitFourthSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] Y) := inferInstance

/-- Local uniform convergence of all four genuine derivative levels identifies
the fourth derivative of the actual value limit. -/
theorem fourth_fderiv_of_locally_uniform_limit
    {Ω : Set E} (hΩ : IsOpen Ω) {u : ℕ → E → Y} {v : E → Y}
    {G : E → E →L[ℝ] Y} {H : E → E →L[ℝ] E →L[ℝ] Y}
    {T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] Y}
    {Q : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] Y}
    (hu : ∀ k, ContDiff ℝ 4 (u k))
    (hv : ∀ x ∈ Ω, Tendsto (fun k => u k x) atTop (𝓝 (v x)))
    (hG : TendstoLocallyUniformlyOn (fun k => fderiv ℝ (u k)) G atTop Ω)
    (hH : TendstoLocallyUniformlyOn (fun k => fderiv ℝ (fderiv ℝ (u k))) H atTop Ω)
    (hT : TendstoLocallyUniformlyOn (fun k => fderiv ℝ (fderiv ℝ (fderiv ℝ (u k)))) T atTop Ω)
    (hQ : TendstoLocallyUniformlyOn
      (fun k => fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (u k))))) Q atTop Ω) :
    ∀ x ∈ Ω, fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ v))) x = Q x := by
  have hthree := third_fderiv_of_locally_uniform_limit hΩ
    (fun k => (hu k).of_le (by norm_num)) hv hG hH hT
  have hd (x) (hx : x ∈ Ω) : HasFDerivAt T (Q x) x :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn hΩ hQ
      (fun k x _ => (((((hu k).fderiv_right (m := 3) (by norm_num)).fderiv_right
        (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)).differentiable
          (by norm_num) x).hasFDerivAt)
      (fun x hx => hT.tendsto_at hx) hx
  intro x hx
  have he : fderiv ℝ (fderiv ℝ (fderiv ℝ v)) =ᶠ[𝓝 x] T :=
    Filter.eventually_of_mem (hΩ.mem_nhds hx) (fun y hy => hthree y hy)
  exact he.fderiv_eq.trans (hd x hx).fderiv

theorem contDiffOn_four_of_locally_uniform_derivatives
    {Ω : Set E} (hΩ : IsOpen Ω) {u : ℕ → E → Y} {v : E → Y}
    {G : E → E →L[ℝ] Y} {H : E → E →L[ℝ] E →L[ℝ] Y}
    {T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] Y}
    {Q : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] Y}
    (hu : ∀ k, ContDiff ℝ 4 (u k))
    (hv : ∀ x ∈ Ω, Tendsto (fun k => u k x) atTop (𝓝 (v x)))
    (hG : TendstoLocallyUniformlyOn (fun k => fderiv ℝ (u k)) G atTop Ω)
    (hH : TendstoLocallyUniformlyOn (fun k => fderiv ℝ (fderiv ℝ (u k))) H atTop Ω)
    (hT : TendstoLocallyUniformlyOn (fun k => fderiv ℝ (fderiv ℝ (fderiv ℝ (u k)))) T atTop Ω)
    (hQ : TendstoLocallyUniformlyOn
      (fun k => fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (u k))))) Q atTop Ω) :
    ContDiffOn ℝ 4 v Ω := by
  have hv' (x) (hx : x ∈ Ω) : HasFDerivAt v (G x) x :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn hΩ hG
      (fun k x _ => ((hu k).differentiable (by norm_num) x).hasFDerivAt) hv hx
  have hGthree : ContDiffOn ℝ 3 G Ω :=
    contDiffOn_three_of_locally_uniform_derivatives hΩ
      (fun k => (hu k).fderiv_right (by norm_num)) (fun x hx => hG.tendsto_at hx) hH hT hQ
  change ContDiffOn ℝ (3+1) v Ω
  rw [contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
  exact ⟨fun x hx => (hv' x hx).differentiableAt.differentiableWithinAt, by simp,
    hGthree.congr (fun x hx => (hv' x hx).fderiv)⟩

end OAI.Analysis.PDE.Dirichlet
