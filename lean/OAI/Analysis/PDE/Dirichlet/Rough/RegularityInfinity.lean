import OAI.Analysis.Calculus.SmoothExtension.Periodic.Infinity
import OAI.Analysis.PDE.Dirichlet.Rough.RegularityGlobal

noncomputable section
open Set Filter Module
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- Actual local C∞ representatives glue to one smooth periodic global
representative on the whole closed periodic domain. -/
theorem exists_smooth_periodic_representative_of_local_regularities
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {C : Set V} (hC : IsCompact C)
    {r : E → ℝ} (hr : Continuous r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (f : E → ℝ) (hfp : LatticePeriodic e b f)
    (hint : ∀ x, r x < 0 → ContDiffAt ℝ ∞ f x)
    (hbd : ∀ a, r a = 0 → ∃ O : Set E, IsOpen O ∧ a ∈ O ∧
      ∃ g : E → ℝ, ContDiffOn ℝ ∞ g O ∧ ∀ x ∈ O, r x ≤ 0 → g x = f x) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ LatticePeriodic e b g ∧
      ∀ x, r x ≤ 0 → g x = f x := by
  apply OAI.Analysis.Calculus.SmoothExtension.exists_latticePeriodic_smooth_sublevel_extension_on
    e b hC hr hrp hbounded f hfp
  intro x hx
  by_cases hi : r x < 0
  · refine ⟨{x | r x < 0},isOpen_lt hr continuous_const,hi,f,?_,?_⟩
    · intro y hy
      exact (hint y hy).contDiffWithinAt
    · intro y hy hyr
      rfl
  · exact hbd x (le_antisymm hx (le_of_not_gt hi))

/-- The smooth representative preserves the complete two-jet, including
on the boundary, and thus preserves the actual second-order PDE. -/
theorem exists_smooth_periodic_representative_with_jets
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P) {C : Set V} (hC : IsCompact C)
    {r : E → ℝ} (hr : ContDiff ℝ 1 r) (hrp : LatticePeriodic e b r)
    (hbounded : ∀ x, r x ≤ 0 → (e x).2 ∈ C)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) (hfp : LatticePeriodic e b f)
    (hint : ∀ x, r x < 0 → ContDiffAt ℝ ∞ f x)
    (hbd : ∀ a, r a = 0 → ∃ O : Set E, IsOpen O ∧ a ∈ O ∧
      ∃ g : E → ℝ, ContDiffOn ℝ ∞ g O ∧ ∀ x ∈ O, r x ≤ 0 → g x = f x) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ LatticePeriodic e b g ∧
      (∀ x, r x ≤ 0 → g x = f x) ∧
      (∀ x, r x ≤ 0 → fderiv ℝ g x = fderiv ℝ f x) ∧
      (∀ x, r x ≤ 0 → fderiv ℝ (fderiv ℝ g) x = fderiv ℝ (fderiv ℝ f) x) := by
  obtain ⟨g,hg,hgp,hge⟩ := exists_smooth_periodic_representative_of_local_regularities
    e b hC hr.continuous hrp hbounded f hfp hint hbd
  have hclosure : {x | r x ≤ 0} ⊆ closure {x | r x < 0} := by
    rw [OAI.Analysis.PDE.Weak.closure_strict_sublevel_of_regular r hr hreg]
  have hjet := first_second_eqOn_of_eqOn_dense_interior
    (isOpen_lt hr.continuous continuous_const)
    (show {x | r x < 0} ⊆ {x | r x ≤ 0} by
      intro x hx
      change r x < 0 at hx
      change r x ≤ 0
      exact hx.le)
    hclosure (hg.of_le (by simp)) hf (fun x hx => hge x hx)
  exact ⟨g,hg,hgp,hge,fun x hx => hjet.1 hx,fun x hx => hjet.2 hx⟩

end OAI.Analysis.PDE.Dirichlet
