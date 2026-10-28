import OAI.Analysis.PDE.Dirichlet.Periodic.SchauderAbsorption
import OAI.Analysis.Normed.Function.Holder.Banach.Construct

open Set Metric Module
open scoped BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E P V F ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

/-- Local Hölder regularity on the closed domain gives an actual global
periodic Hölder field. In particular, a continuous fourth derivative does
not need a fifth derivative, or an a priori global Hölder bound. -/
theorem exists_periodic_holder_field_of_local
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (g : E → F) (hg : Continuous g) (hgp : LatticePeriodic e b g)
    {α : ℝ} (hα : 0 < α)
    (hlocal : ∀ x, r x ≤ 0 → ∃ δ > 0, ∃ C ≥ 0,
      ∀ y ∈ closedBall x δ, r y ≤ 0 → ∀ z ∈ closedBall x δ, r z ≤ 0 →
        ‖g y-g z‖ ≤ C*dist y z^α) :
    ∃ T : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α,
      ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = g x := by
  let S := cthickening 1 (latticeSublevelCell e b K r) ∩ {x | r x ≤ 0}
  have hS : IsCompact S :=
    (isCompact_latticeSublevelCell e b hK hr).cthickening.inter_right
      (isClosed_le hr continuous_const)
  obtain ⟨M,hM⟩ := hS.exists_bound_of_continuousOn hg.continuousOn
  have hloc : ∀ x ∈ S, ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ (_ : Unit) y, y ∈ S → dist y x ≤ δ →
        ‖g y‖ ≤ C*1 ∧ ∀ z, z ∈ S → dist z x ≤ δ →
          ‖g y-g z‖ ≤ C*1*dist y z^α := by
    intro x hx
    obtain ⟨δ,hδ,C,hC,hloc⟩ := hlocal x hx.2
    refine ⟨δ,1+max M C,hδ,by have := le_max_right M C; linarith,?_⟩
    intro _ y hy hyx
    constructor
    · have hMy := hM y hy
      have hMC := le_max_left M C
      simpa only [mul_one] using (show ‖g y‖ ≤ 1+max M C by linarith)
    · intro z hz hzx
      have hh := hloc y hyx hy.2 z hzx hz.2
      apply hh.trans
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg dist_nonneg _)
      have hMC := le_max_right M C
      simpa only [mul_one] using (show C ≤ 1+max M C by linarith)
  obtain ⟨C,hC,hn,hh⟩ := OAI.Analysis.PDE.Elliptic.compact_family_fixed_holder_of_local hS
    (fun _ : Unit => g) (fun _ => (1 : ℝ)) (fun _ => zero_le_one) hα hloc
  have hnorm : ∀ x, r x ≤ 0 → ‖g x‖ ≤ C :=
    lattice_norm_le_of_thickened_cell e b hrp hbounded g hgp
      (fun x hx => by simpa only [mul_one] using hn () x hx)
  have hholder := lattice_holder_of_thickened_cell e b hrp hbounded
    (fun _ : Unit => g) (fun _ => hgp) hα.le hC.le hC.le
    (fun _ => hnorm) (fun _ x hx y hy => by
      simpa only [mul_one] using hh () x hx y hy)
  let g₀ : {x | r x ≤ 0} →ᵇ F := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => g x) (hg.comp continuous_subtype_val) C (fun x => hnorm x x.property)
  have hg₀ : ∀ x y, ‖g₀ x-g₀ y‖ ≤ (C+2*C)*dist x y^α :=
    fun x y => hholder () x x.property y y.property
  exact ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα.le g₀ hg₀, fun _ => rfl⟩

end OAI.Analysis.PDE.Dirichlet
