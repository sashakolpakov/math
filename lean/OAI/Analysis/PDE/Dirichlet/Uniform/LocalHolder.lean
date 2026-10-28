import OAI.Analysis.PDE.Dirichlet.Periodic.LocalHolder

open Set Metric Module
open scoped BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E P V F ι A : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

/-- Uniform local estimates on the lifted closed domain give uniform
global Hölder fields. Each local radius and constant is fixed before the
member of the family is selected. -/
theorem exists_uniform_periodic_holder_fields_of_local
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {K : Set V} (hK : IsCompact K)
    {r : E → ℝ} (hr : Continuous r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ K)
    (g : A → E → F) (hg : ∀ a, Continuous (g a)) (hgp : ∀ a, LatticePeriodic e b (g a))
    {α : ℝ} (hα : 0 < α)
    (hlocal : ∀ x, r x ≤ 0 → ∃ δ > 0, ∃ C > 0,
      ∀ a y, y ∈ closedBall x δ → r y ≤ 0 →
        ‖g a y‖ ≤ C ∧ ∀ z, z ∈ closedBall x δ → r z ≤ 0 →
          ‖g a y-g a z‖ ≤ C*dist y z^α) :
    ∃ M > 0, ∀ a, ∃ T : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} F α,
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = g a x) ∧ ‖T‖ ≤ M := by
  let S := cthickening 1 (latticeSublevelCell e b K r) ∩ {x | r x ≤ 0}
  have hS : IsCompact S :=
    (isCompact_latticeSublevelCell e b hK hr).cthickening.inter_right
      (isClosed_le hr continuous_const)
  have hloc : ∀ x ∈ S, ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ a y, y ∈ S → dist y x ≤ δ →
        ‖g a y‖ ≤ C*1 ∧ ∀ z, z ∈ S → dist z x ≤ δ →
          ‖g a y-g a z‖ ≤ C*1*dist y z^α := by
    intro x hx
    obtain ⟨δ,hδ,C,hC,hloc⟩ := hlocal x hx.2
    refine ⟨δ,C,hδ,hC,?_⟩
    intro a y hy hyx
    obtain ⟨hn,hh⟩ := hloc a y hyx hy.2
    refine ⟨by simpa only [mul_one] using hn,?_⟩
    intro z hz hzx
    simpa only [mul_one] using hh z hzx hz.2
  obtain ⟨C,hC,hn,hh⟩ := OAI.Analysis.PDE.Elliptic.compact_family_fixed_holder_of_local hS
    g (fun _ => (1 : ℝ)) (fun _ => zero_le_one) hα hloc
  have hnorm (a) : ∀ x, r x ≤ 0 → ‖g a x‖ ≤ C :=
    lattice_norm_le_of_thickened_cell e b hrp hbounded (g a) (hgp a)
      (fun x hx => by simpa only [mul_one] using hn a x hx)
  have hholder := lattice_holder_of_thickened_cell e b hrp hbounded g hgp hα.le hC.le hC.le
    hnorm (fun a x hx y hy => by simpa only [mul_one] using hh a x hx y hy)
  refine ⟨3*C,by positivity,?_⟩
  intro a
  let g₀ : {x | r x ≤ 0} →ᵇ F := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => g a x) ((hg a).comp continuous_subtype_val) C (fun x => hnorm a x x.property)
  have hg₀ : ∀ x y, ‖g₀ x-g₀ y‖ ≤ (C+2*C)*dist x y^α :=
    fun x y => hholder a x x.property y y.property
  let T := OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα.le g₀ hg₀
  refine ⟨T,fun _ => rfl,?_⟩
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.norm_le_of_bounds hα.le (by positivity)
  · intro x
    exact (hnorm a x x.property).trans (by linarith)
  · intro x y
    change ‖g₀ x-g₀ y‖ ≤ 3*C*dist x y^α
    calc
      _ ≤ (C+2*C)*dist x y^α := hg₀ x y
      _ = _ := by ring

end OAI.Analysis.PDE.Dirichlet
