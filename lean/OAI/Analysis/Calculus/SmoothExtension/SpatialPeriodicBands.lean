import OAI.Analysis.Calculus.SmoothExtension.Periodic.CompactBands

/-! Smooth gluing over open parameter regions, with periodicity only in
the spatial variables. -/
noncomputable section
open Set Filter Function TopologicalSpace Module
open scoped Topology ContDiff Manifold
namespace OAI.Analysis.Calculus.SmoothExtension

open OAI.Analysis.PDE.Dirichlet

variable {Z E P V ι : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

omit [Fintype ι] [FiniteDimensional ℝ E] in
theorem exists_spatially_periodic_smooth_on_of_compact_bands
    (e : E ≃L[ℝ] P × V) (b : Basis ι ℝ P)
    {Ω : Set Z} (hΩ : IsOpen Ω) (K : Set (Z × E)) (u : Z × E → ℝ)
    (hc : ∀ C : Set Z, IsCompact C → C ⊆ Ω →
      ∃ g : Z × E → ℝ, ContDiff ℝ ∞ g ∧
        (∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x ↦ g (z,x))) ∧
        ∀ p ∈ K, p.1 ∈ C → g p = u p) :
    ∃ g : Z × E → ℝ, ContDiffOn ℝ ∞ g (Ω ×ˢ univ) ∧
      (∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun x ↦ g (z,x))) ∧
      ∀ p ∈ K, p.1 ∈ Ω → g p = u p := by
  let L : Submodule.span ℤ (Set.range b) →+ Z × E :=
    (0 : Submodule.span ℤ (Set.range b) →+ Z).prod (latticeShiftHom e b)
  have hshift (p : Z × E) (l : Submodule.span ℤ (Set.range b)) :
      p + L l = (p.1, e.symm ((e p.2).1 + (l : P), (e p.2).2)) := by
    apply Prod.ext
    · simp [L]
    · change p.2 + e.symm ((l : P), 0) = _
      simpa only [add_comm] using (OAI.Analysis.PDE.Dirichlet.lattice_translate_eq e p.2 (l : P)).symm
  obtain ⟨g,hg,hgp,hge⟩ := exists_periodic_smooth_on_of_compact_bands
    L Prod.fst contDiff_fst (fun p l ↦ by simp [L]) hΩ K u (by
      intro C hC hCΩ
      obtain ⟨g,hg,hgp,hge⟩ := hc C hC hCΩ
      refine ⟨g,hg,?_,hge⟩
      intro p l
      rw [hshift]
      exact hgp p.1 p.2 l)
  refine ⟨g,?_,?_,hge⟩
  · have hs : (Prod.fst : Z × E → Z) ⁻¹' Ω = Ω ×ˢ univ := by
      ext p
      simp only [mem_preimage, mem_prod, mem_univ, and_true]
    rwa [hs] at hg
  · intro z x l
    simpa only [hshift] using hgp (z,x) l

end OAI.Analysis.Calculus.SmoothExtension
