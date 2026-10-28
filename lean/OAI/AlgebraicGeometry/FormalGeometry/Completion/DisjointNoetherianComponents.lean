import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Connected.Clopen

/-! # Disjoint Noetherian Components -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.DisjointNoetherianComponents.Construction

noncomputable section

/-!
# Completion: disjoint Noetherian irreducible components are connected components
-/

open _root_.TopologicalSpace

variable (X : Type*) [TopologicalSpace X] [NoetherianSpace X]
  (h : ∀ (x : X) {C D : Set X}, C ∈ irreducibleComponents X →
    D ∈ irreducibleComponents X → x ∈ C → x ∈ D → C = D)

include h

/-- A Noetherian irreducible component disjoint from all others is open and closed. -/
theorem disjoint_noetherian_component_isClopen {C : Set X}
    (hC : C ∈ irreducibleComponents X) : IsClopen C := by
  have he : C = (⋃₀ (irreducibleComponents X \ {C}))ᶜ := by
    ext x
    constructor
    · intro hx hx'
      obtain ⟨D, hD, hxD⟩ := hx'
      exact hD.2 (Set.mem_singleton_iff.mpr (h x hD.1 hC hxD hx))
    · intro hx
      have hxC := mem_irreducibleComponent (x := x)
      have he : irreducibleComponent x = C := by
        by_contra hn
        exact hx ⟨irreducibleComponent x,
          ⟨irreducibleComponent_mem_irreducibleComponents x, hn⟩, hxC⟩
      exact he ▸ hxC
  refine ⟨isClosed_of_mem_irreducibleComponents C hC, ?_⟩
  rw [he, Set.sUnion_eq_biUnion]
  exact (NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_biUnion
    (fun D hD => isClosed_of_mem_irreducibleComponents D hD.1)).isOpen_compl

/-- With disjoint irreducible components, each connected component is irreducible. -/
theorem disjoint_noetherian_connectedComponent_isIrreducible (x : X) :
    IsIrreducible (connectedComponent x) := by
  have hc := irreducibleComponent_mem_irreducibleComponents x
  have he : connectedComponent x = irreducibleComponent x :=
    Set.Subset.antisymm
      ((disjoint_noetherian_component_isClopen X h hc).connectedComponent_subset
        mem_irreducibleComponent)
      (hc.1.isConnected.isPreconnected.subset_connectedComponent mem_irreducibleComponent)
  rw [he]
  exact hc.1

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.DisjointNoetherianComponents.Construction
