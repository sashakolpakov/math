import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober

/-! # Noetherian Closed Points -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.NoetherianClosedPoints.Construction

/-! # Completion: a Noetherian sober space with closed points is finite -/

open _root_.TopologicalSpace

universe u

/-- In a Noetherian sober space whose points are closed, every irreducible component
is a singleton, so the whole space is finite. -/
theorem finite_of_noetherian_quasiSober_t1 (X : Type u) [TopologicalSpace X]
    [NoetherianSpace X] [QuasiSober X] [T1Space X] : Finite X := by
  classical
  have : Finite (irreducibleComponents X) := NoetherianSpace.finite_irreducibleComponents
  let g : irreducibleComponents X → X := fun C => C.property.1.genericPoint
  apply Finite.of_surjective g
  intro x
  let C : irreducibleComponents X := ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  have h : closure {g C} = C.val := C.property.1.closure_genericPoint
    (isClosed_of_mem_irreducibleComponents _ C.property)
  rw [closure_singleton] at h
  refine ⟨C, ?_⟩
  have hx : x ∈ ({g C} : Set X) := h ▸ mem_irreducibleComponent
  exact (Set.mem_singleton_iff.mp hx).symm

end OAI.AlgebraicGeometry.FormalGeometry.Completion.NoetherianClosedPoints.Construction
