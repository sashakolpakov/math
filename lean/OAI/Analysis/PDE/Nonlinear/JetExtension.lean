import OAI.Analysis.PDE.Nonlinear.CutoffJet
import OAI.Analysis.PDE.Dirichlet.ComparisonLocal

/-! Local C²,α data admit compactly supported extensions with genuine Hölder jets. -/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

local instance extensionFirstGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance extensionFirstSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance extensionSecondGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance extensionSecondSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem exists_C2_holder_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ProperSpace E] [HasContDiffBump E]
    (u : E → ℝ) (x₀ : E) (hu : ContDiffAt ℝ 2 u x₀) {R α C : ℝ}
    (hR : 0 < R) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    (hh : ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R,
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ C * ‖x - y‖ ^ α) :
    ∃ g : E → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ g =ᶠ[𝓝 x₀] u ∧
      ∃ (V : OAI.Analysis.Normed.Function.Holder.HolderMap E (E →L[ℝ] ℝ) α) (H : OAI.Analysis.Normed.Function.Holder.HolderMap E (E →L[ℝ] E →L[ℝ] ℝ) α),
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = fderiv ℝ g x) ∧
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = fderiv ℝ (fderiv ℝ g) x) := by
  obtain ⟨g₀, hg₀, heq⟩ := OAI.Analysis.PDE.Dirichlet.exists_contDiff_extension_near_point hu
  have hevent : ∀ᶠ x in 𝓝 x₀, g₀ x = u x ∧ x ∈ ball x₀ R :=
    heq.and (ball_mem_nhds x₀ hR)
  obtain ⟨ε, hε, hεprop⟩ := Metric.eventually_nhds_iff.mp hevent
  let χ : ContDiffBump x₀ := ⟨ε / 8, ε / 4, by positivity, by linarith only [hε]⟩
  let g : E → ℝ := fun x => χ x * g₀ x
  have hg : ContDiff ℝ 2 g := χ.contDiff.mul hg₀
  have hgc : HasCompactSupport g := χ.hasCompactSupport.mul_right
  have hgu : g =ᶠ[𝓝 x₀] u := by
    filter_upwards [χ.eventuallyEq_one, heq] with x hx hx'
    change χ x * g₀ x = u x
    simpa only [Pi.one_apply, hx, one_mul] using hx'
  have hsmall (x) (hx : x ∈ closedBall x₀ (ε / 2)) : x ∈ ball x₀ ε := by
    change dist x x₀ < ε
    exact lt_of_le_of_lt (show dist x x₀ ≤ ε / 2 from hx) (by linarith only [hε])
  have hD (x) (hx : x ∈ ball x₀ ε) :
      fderiv ℝ (fderiv ℝ g₀) x = fderiv ℝ (fderiv ℝ u) x := by
    have hgerm : g₀ =ᶠ[𝓝 x] u := by
      filter_upwards [isOpen_ball.mem_nhds hx] with y hy
      exact (hεprop hy).1
    exact (hgerm.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
  obtain ⟨H, hH⟩ := exists_cutoff_hessian_holder (χ : E → ℝ) g₀ χ.contDiff χ.hasCompactSupport hg₀
    x₀ (r := ε / 4) (R := ε / 2) (by linarith only [hε]) (by positivity)
    hα hα1 hC (fun x => ⟨χ.nonneg, χ.le_one⟩)
    (by
      intro x hx
      apply image_eq_zero_of_notMem_tsupport
      simpa only [χ.tsupport_eq] using hx)
    (by
      intro x hx y hy
      rw [hD x (hsmall x hx), hD y (hsmall y hy)]
      exact hh x (hεprop (hsmall x hx)).2 y (hεprop (hsmall y hy)).2)
  let V := OAI.Analysis.PDE.Schauder.compactC1Holder (fderiv ℝ g) (hg.fderiv_right (m := 1) (by norm_num))
    (hgc.fderiv (𝕜 := ℝ)) hα hα1
  exact ⟨g, hg, hgc, hgu, V, H, fun _ => rfl, hH⟩

theorem exists_C2_compact_extension
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [HasContDiffBump E]
    (f : E → ℝ) (x₀ : E) (hf : ContDiffAt ℝ 2 f x₀) {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ g : E → ℝ, ContDiff ℝ 2 g ∧ g =ᶠ[𝓝 x₀] f ∧
      ∃ D : OAI.Analysis.Normed.Function.Holder.HolderMap E (E →L[ℝ] ℝ) α, ∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = fderiv ℝ g x := by
  obtain ⟨g₀, hg₀, heq⟩ := OAI.Analysis.PDE.Dirichlet.exists_contDiff_extension_near_point hf
  let χ : ContDiffBump x₀ := ⟨1, 2, by norm_num, by norm_num⟩
  let g : E → ℝ := fun x => χ x * g₀ x
  have hg : ContDiff ℝ 2 g := χ.contDiff.mul hg₀
  have hgc : HasCompactSupport g := χ.hasCompactSupport.mul_right
  have hgf : g =ᶠ[𝓝 x₀] f := by
    filter_upwards [χ.eventuallyEq_one, heq] with x hx hx'
    change χ x * g₀ x = f x
    simpa only [Pi.one_apply, hx, one_mul] using hx'
  let D := OAI.Analysis.PDE.Schauder.compactC1Holder (fderiv ℝ g) (hg.fderiv_right (m := 1) (by norm_num))
    (hgc.fderiv (𝕜 := ℝ)) hα hα1
  exact ⟨g, hg, hgf, D, fun _ => rfl⟩

end OAI.Analysis.PDE.Nonlinear
