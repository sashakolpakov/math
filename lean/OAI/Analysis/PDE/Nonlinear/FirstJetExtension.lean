import OAI.Analysis.PDE.Nonlinear.CutoffHolder
import OAI.Analysis.PDE.Dirichlet.ComparisonLocal

/-! A local C¹,α field extends to a compact C¹ field with its true Hölder derivative. -/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance firstJetScalarGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance firstJetScalarSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance firstJetGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance firstJetSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance

theorem exists_C1_holder_extension [FiniteDimensional ℝ E] [ProperSpace E] [HasContDiffBump E]
    (f : E → F) (x₀ : E) (hf : ContDiffAt ℝ 1 f x₀) {R α C : ℝ}
    (hR : 0 < R) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    (hh : ∀ x ∈ ball x₀ R, ∀ y ∈ ball x₀ R,
      ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ C * ‖x - y‖ ^ α) :
    ∃ g : E → F, ContDiff ℝ 1 g ∧ HasCompactSupport g ∧ g =ᶠ[𝓝 x₀] f ∧
      ∃ (V : OAI.Analysis.Normed.Function.Holder.HolderMap E F α) (D : OAI.Analysis.Normed.Function.Holder.HolderMap E (E →L[ℝ] F) α),
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = g x) ∧ (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = fderiv ℝ g x) := by
  obtain ⟨g₀, hg₀, heqall⟩ := OAI.Analysis.PDE.Elliptic.exists_contDiff_extension_near_compact
    (K := {x₀}) (k := 1) isCompact_singleton (fun x hx => by
      have hx' : x = x₀ := mem_singleton_iff.mp hx
      subst x
      convert! hf using 1)
  have heq : g₀ =ᶠ[𝓝 x₀] f := heqall x₀ (mem_singleton x₀)
  have hg₀' : ContDiff ℝ 1 g₀ := by convert! hg₀ using 1
  have hevent : ∀ᶠ x in 𝓝 x₀, g₀ x = f x ∧ x ∈ ball x₀ R := heq.and (ball_mem_nhds x₀ hR)
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp hevent
  let χ : ContDiffBump x₀ := ⟨ε / 8, ε / 4, by positivity, by linarith only [hε]⟩
  let g : E → F := fun x => χ x • g₀ x
  have hg : ContDiff ℝ 1 g := χ.contDiff.smul hg₀'
  have hgc : HasCompactSupport g := χ.hasCompactSupport.smul_right
  have hgf : g =ᶠ[𝓝 x₀] f := by
    filter_upwards [χ.eventuallyEq_one, heq] with x hx hx'
    change χ x • g₀ x = f x
    simpa only [Pi.one_apply, hx, one_smul] using hx'
  have hsmall (x) (hx : x ∈ closedBall x₀ (ε / 2)) : x ∈ ball x₀ ε := by
    change dist x x₀ < ε
    exact lt_of_le_of_lt (show dist x x₀ ≤ ε / 2 from hx) (by linarith only [hε])
  have hD (x) (hx : x ∈ ball x₀ ε) : fderiv ℝ g₀ x = fderiv ℝ f x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    exact (he hy).1
  have hcD : Continuous (fderiv ℝ g₀) := (hg₀'.fderiv_right (m := 0) (by norm_num)).continuous
  obtain ⟨H, hH⟩ := exists_cutoff_holder_field (χ : E → ℝ) (fderiv ℝ g₀) χ.contDiff
    χ.hasCompactSupport hcD x₀ (r := ε / 4) (R := ε / 2) (by linarith only [hε])
    (by positivity) hα hα1 hC (fun x => ⟨χ.nonneg, χ.le_one⟩)
    (by
      intro x hx
      apply image_eq_zero_of_notMem_tsupport
      simpa only [χ.tsupport_eq] using hx)
    (by
      intro x hx y hy
      rw [hD x (hsmall x hx), hD y (hsmall y hy)]
      exact hh x (he (hsmall x hx)).2 y (he (hsmall y hy)).2)
  let T := fun x => (fderiv ℝ (χ : E → ℝ) x).smulRight (g₀ x)
  have hT : ContDiff ℝ 1 T :=
    ((χ.contDiff : ContDiff ℝ 2 (χ : E → ℝ)).fderiv_right (by norm_num)).smulRight hg₀'
  have hTc : HasCompactSupport T := by
    apply χ.hasCompactSupport.mono'
    intro x hx
    by_contra hnot
    apply hx
    change (fderiv ℝ (χ : E → ℝ) x).smulRight (g₀ x) = 0
    rw [fderiv_of_notMem_tsupport ℝ hnot]
    ext v
    simp
  let D := H + OAI.Analysis.PDE.Schauder.compactC1Holder T hT hTc hα hα1
  refine ⟨g, hg, hgc, hgf, OAI.Analysis.PDE.Schauder.compactC1Holder g hg hgc hα hα1, D, fun _ => rfl, ?_⟩
  intro x
  change OAI.Analysis.Normed.Function.Holder.HolderMap.value H x + T x = fderiv ℝ g x
  rw [hH x]
  exact (fderiv_fun_smul (χ.contDiff.differentiable one_ne_zero x) (hg₀'.differentiable one_ne_zero x)).symm

end OAI.Analysis.PDE.Nonlinear
