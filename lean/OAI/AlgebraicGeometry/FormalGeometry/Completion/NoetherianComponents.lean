import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Connected.Clopen

/-! # Noetherian Components -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.NoetherianComponents.Construction

noncomputable section

/-! # Completion: connected components of Noetherian spaces are finite and open -/

open _root_.TopologicalSpace

universe u

variable (X : Type u) [TopologicalSpace X] [NoetherianSpace X]

/-- A Noetherian space has finitely many connected components. -/
theorem noetherian_connectedComponents_finite : Finite (ConnectedComponents X) := by
  classical
  have : Finite (irreducibleComponents X) := NoetherianSpace.finite_irreducibleComponents
  let point : irreducibleComponents X → X := fun C => C.property.1.nonempty.choose
  let g : irreducibleComponents X → ConnectedComponents X := fun C => (point C : ConnectedComponents X)
  apply Finite.of_surjective g
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  let C : irreducibleComponents X := ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  refine ⟨C, ?_⟩
  apply Eq.symm
  apply ConnectedComponents.coe_eq_coe'.mpr
  exact C.property.1.isConnected.isPreconnected.subset_connectedComponent
    C.property.1.nonempty.choose_spec mem_irreducibleComponent

/-- The finite quotient by connected components has the discrete topology. -/
theorem noetherian_connectedComponents_discrete : DiscreteTopology (ConnectedComponents X) := by
  have := noetherian_connectedComponents_finite X
  have : T1Space (ConnectedComponents X) := ⟨fun c => by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rw [← ConnectedComponents.isQuotientMap_coe.isClosed_preimage,
      connectedComponents_preimage_singleton]
    exact isClosed_connectedComponent⟩
  infer_instance

/-- Each connected component of a Noetherian space is open and closed. -/
theorem noetherian_connectedComponent_isClopen (x : X) : IsClopen (connectedComponent x) := by
  have := noetherian_connectedComponents_discrete X
  exact ⟨isClosed_connectedComponent, ConnectedComponents.discreteTopology_iff.mp this x⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.NoetherianComponents.Construction
