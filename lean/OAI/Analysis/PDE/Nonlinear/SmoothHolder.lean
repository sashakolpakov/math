import OAI.Analysis.PDE.Nonlinear.JetExtension
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Interior

/-! Local C¹ coefficient fields yield honest Hölder extensions and local Schauder bounds. -/

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

theorem exists_C1_holder_germ
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [HasContDiffBump E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x₀ : E) (hf : ContDiffAt ℝ 1 f x₀) {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ H : OAI.Analysis.Normed.Function.Holder.HolderMap E F α, OAI.Analysis.Normed.Function.Holder.HolderMap.value H =ᶠ[𝓝 x₀] f := by
  obtain ⟨g₀, hg₀, heq⟩ := OAI.Analysis.PDE.Elliptic.exists_contDiff_extension_near_compact
    (K := {x₀}) (k := 1) isCompact_singleton (fun x hx => by
      have hx' : x = x₀ := mem_singleton_iff.mp hx
      subst x
      convert! hf using 1)
  let χ : ContDiffBump x₀ := ⟨1, 2, by norm_num, by norm_num⟩
  let g : E → F := fun x => χ x • g₀ x
  have hg : ContDiff ℝ 1 g := χ.contDiff.smul hg₀
  have hgc : HasCompactSupport g := χ.hasCompactSupport.smul_right
  refine ⟨OAI.Analysis.PDE.Schauder.compactC1Holder g hg hgc hα hα1, ?_⟩
  filter_upwards [χ.eventuallyEq_one, heq x₀ (mem_singleton x₀)] with x hx hx'
  change χ x • g₀ x = f x
  simpa only [Pi.one_apply, hx, one_smul] using hx'

theorem local_C1_coefficient_schauder {m : ℕ} (hm : 3 ≤ m) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    (A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ)
    (u f : EuclideanSpace ℝ (Fin m) → ℝ) (x₀ : EuclideanSpace ℝ (Fin m))
    (hA : ContDiffAt ℝ 1 A x₀) (hu : ContDiffAt ℝ 2 u x₀) (hf : ContDiffAt ℝ 1 f x₀)
    (hPD : ∀ᶠ x in 𝓝 x₀, (A x).PosDef)
    (hPDE : ∀ᶠ x in 𝓝 x₀, OAI.Analysis.PDE.Schauder.nondivergenceOperator A u x = f x) :
    ∃ r > 0, ∃ C > 0, ∀ x ∈ ball x₀ r, ∀ y ∈ ball x₀ r,
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ C * ‖x - y‖ ^ α := by
  obtain ⟨B, hB⟩ := exists_C1_holder_germ A x₀ hA hα.le hα1.le
  obtain ⟨F, hF⟩ := exists_C1_holder_germ f x₀ hf hα.le hα1.le
  have hevent : ∀ᶠ x in 𝓝 x₀, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = A x ∧ OAI.Analysis.Normed.Function.Holder.HolderMap.value F x = f x ∧
      (A x).PosDef ∧ OAI.Analysis.PDE.Schauder.nondivergenceOperator A u x = f x ∧ ContDiffAt ℝ 2 u x := by
    filter_upwards [hB, hF, hPD, hPDE, hu.eventually (by simp)] with x hb hf hp hq hu
    exact ⟨hb, hf, hp, hq, hu⟩
  obtain ⟨R, hR, he⟩ := Metric.eventually_nhds_iff.mp hevent
  apply OAI.Analysis.PDE.Schauder.elliptic_interior_schauder hm hα hα1 B F (ball x₀ R) isOpen_ball u
    (fun x hx => (he hx).2.2.2.2.contDiffWithinAt) _ _ x₀ (mem_ball_self hR)
  · intro x hx
    rw [(he hx).1]
    exact (he hx).2.2.1
  · intro x hx
    change (∑ i, ∑ j, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x i j *
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) = _
    rw [(he hx).1, (he hx).2.1]
    exact (he hx).2.2.2.1

end OAI.Analysis.PDE.Nonlinear
