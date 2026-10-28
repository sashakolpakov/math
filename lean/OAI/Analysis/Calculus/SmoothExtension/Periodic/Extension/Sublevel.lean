import OAI.Analysis.Calculus.SmoothExtension.Periodic.Extension.Lattice

open Set Filter Module
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.Calculus.SmoothExtension

open OAI.Analysis.PDE.Dirichlet

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- The actual closed periodic Dirichlet domain: a transverse bound and
local C^q representatives suffice for a global periodic C^q extension. -/
theorem exists_latticePeriodic_contDiff_sublevel_extension
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {r : E → ℝ} (hr : Continuous r)
    (hrper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀x, r x ≤ 0 → (e x).2 ∈ C)
    (q : ℕ) (u : E → ℝ) (huper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b u)
    (hl : ∀x, r x ≤ 0 → ∃U : Set E, IsOpen U ∧ x ∈ U ∧
      ∃g : E → ℝ, ContDiff ℝ q g ∧ ∀y ∈ U, r y ≤ 0 → g y = u y) :
    ∃g : E → ℝ, ContDiff ℝ q g ∧ OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b g ∧
      ∀x, r x ≤ 0 → g x = u x := by
  apply exists_latticePeriodic_contDiff_extension_of_local e b
    (isClosed_le hr continuous_const) (OAI.Analysis.PDE.Dirichlet.isCompact_latticeSublevelCell e b hC hr)
    (hrper.comp (fun t ↦ t ≤ 0))
    (fun x hx ↦ OAI.Analysis.PDE.Dirichlet.latticeRepresentative_mem_sublevelCell e b hrper hbounded hx) q u huper
  intro x hx
  obtain ⟨U,hU,hxU,g,hg,hgu⟩ := hl x hx
  exact ⟨U,hU,hxU,g,hg,fun y hy ↦ hgu y hy.2 hy.1⟩

/-- The patch representatives may instead be smooth only on their
respective open patches, as produced by a boundary chart. -/
theorem exists_latticePeriodic_contDiff_sublevel_extension_on
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {C : Set V} (hC : IsCompact C) {r : E → ℝ} (hr : Continuous r)
    (hrper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hbounded : ∀x, r x ≤ 0 → (e x).2 ∈ C)
    (q : ℕ) (u : E → ℝ) (huper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b u)
    (hl : ∀x, r x ≤ 0 → ∃U : Set E, IsOpen U ∧ x ∈ U ∧
      ∃g : E → ℝ, ContDiffOn ℝ q g U ∧ ∀y ∈ U, r y ≤ 0 → g y = u y) :
    ∃g : E → ℝ, ContDiff ℝ q g ∧ OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b g ∧
      ∀x, r x ≤ 0 → g x = u x := by
  obtain ⟨g,hg,hgu⟩ := exists_contDiff_extension_of_local_on
    (isClosed_le hr continuous_const) q u (by
      intro x hx
      obtain ⟨U,hU,hxU,g,hg,hgu⟩ := hl x hx
      exact ⟨U,hU,hxU,g,hg,fun y hy ↦ hgu y hy.2 hy.1⟩)
  apply exists_latticePeriodic_contDiff_sublevel_extension e b hC hr hrper hbounded q u huper
  intro x hx
  exact ⟨univ,isOpen_univ,mem_univ x,g,hg,fun y _ hy ↦ hgu y hy⟩

end OAI.Analysis.Calculus.SmoothExtension
