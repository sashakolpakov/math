import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReducedClosedSubschemes
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Reduced Component Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReducedComponentFiniteness

noncomputable section

/-! Finiteness of a noetherian scheme follows when all its reduced irreducible components are points. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (X : Scheme.{u})

theorem reducedClosedSubscheme_irreducible (Z : TopologicalSpace.Closeds X)
    (hZ : IsIrreducible (Z : Set X)) : IrreducibleSpace (ReducedClosedSubschemes.reducedClosedSubscheme X Z) := by
  change IrreducibleSpace Z
  exact Subtype.irreducibleSpace hZ

theorem finite_of_reduced_components_subsingleton [IsNoetherian X]
    (h : ∀ (Z : Set X) (hZ : Z ∈ irreducibleComponents X),
      Subsingleton (ReducedClosedSubschemes.reducedClosedSubscheme X ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩)) : Finite X := by
  have hZ (Z : Set X) (hZ : Z ∈ irreducibleComponents X) : Z.Finite := by
    let C : TopologicalSpace.Closeds X := ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩
    let : Subsingleton (ReducedClosedSubschemes.reducedClosedSubscheme X C) := h Z hZ
    have hr : Set.range (ReducedClosedSubschemes.reducedClosedInclusion X C) = Z := ReducedClosedSubschemes.reducedClosedInclusion_range X C
    exact hr ▸ Set.finite_range (ReducedClosedSubschemes.reducedClosedInclusion X C)
  apply Finite.of_finite_univ
  rw [← sUnion_irreducibleComponents (X := X)]
  exact TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.sUnion hZ

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ReducedComponentFiniteness
