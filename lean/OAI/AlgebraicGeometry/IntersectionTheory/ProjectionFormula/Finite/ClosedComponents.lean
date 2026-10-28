import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

/-! # Closed Components -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ClosedComponents

noncomputable section

/-! A fixed closed subset of a Noetherian scheme has a native
finite collection of its global irreducible component supports. -/

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

variable (Z : Scheme) [NoetherianSpace Z] (S : Closeds Z)

def components : Finset (IrreducibleCloseds Z) := by
  let : NoetherianSpace S := NoetherianSpace.set (S : Set Z)
  let : Finite (irreducibleComponents S) :=
    (NoetherianSpace.finite_irreducibleComponents (α := S)).to_subtype
  exact (Set.finite_range (CycleClass.Thom.IntersectionGeometry.closedComponentSupport Z S)).toFinset

theorem mem_iff (C : IrreducibleCloseds Z) : C ∈ components Z S ↔
    ∃ D : irreducibleComponents S, CycleClass.Thom.IntersectionGeometry.closedComponentSupport Z S D = C := by
  simp only [components, Set.Finite.mem_toFinset, Set.mem_range]

theorem subset (C : IrreducibleCloseds Z) (hC : C ∈ components Z S) : (C : Set Z) ⊆ S := by
  obtain ⟨D, rfl⟩ := (mem_iff Z S C).mp hC
  exact Supports.closedComponentSupport_subset Z S D

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.ClosedComponents
