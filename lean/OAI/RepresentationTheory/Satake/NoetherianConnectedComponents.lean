import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Connected.Clopen

/-! # Noetherian Connected Components -/

namespace OAI.RepresentationTheory.Satake.NoetherianConnectedComponents.GL.Zariski

noncomputable section

/-! Connected components in a Noetherian space are open. The
complement is a finite union of disjoint irreducible components. -/

open _root_.TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

theorem irreducibleComponent_subset_connectedComponent {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) {x y : X} (hy : y ∈ Z) (hyx : y ∈ connectedComponent x) :
    Z ⊆ connectedComponent x := by
  have hsub := hZ.1.2.isPreconnected.subset_connectedComponent hy
  rwa [← connectedComponent_eq hyx] at hsub

theorem noetherian_connectedComponent_isOpen [NoetherianSpace X] (x : X) :
    IsOpen (connectedComponent x) := by
  let S : Set (Set X) := {Z | Z ∈ irreducibleComponents X ∧ ¬ Z ⊆ connectedComponent x}
  have hS : S.Finite := NoetherianSpace.finite_irreducibleComponents.subset (fun _ h => h.1)
  have he : (connectedComponent x)ᶜ = ⋃₀ S := by
    ext y
    constructor
    · intro hy
      exact Set.mem_sUnion.mpr ⟨irreducibleComponent y,
        ⟨irreducibleComponent_mem_irreducibleComponents y,
          fun h => hy (h (mem_irreducibleComponent (x := y)))⟩, mem_irreducibleComponent (x := y)⟩
    · intro hy hyx
      obtain ⟨Z, hZ, hyZ⟩ := Set.mem_sUnion.mp hy
      exact hZ.2 (irreducibleComponent_subset_connectedComponent hZ.1 hyZ hyx)
  apply isClosed_compl_iff.mp
  rw [he, Set.sUnion_eq_biUnion]
  exact hS.isClosed_biUnion (fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1)

theorem noetherian_connectedComponents_finite [NoetherianSpace X] : Finite (ConnectedComponents X) := by
  have : DiscreteTopology (ConnectedComponents X) :=
    ConnectedComponents.discreteTopology_iff.mpr noetherian_connectedComponent_isOpen
  have : NoetherianSpace (ConnectedComponents X) := noetherianSpace_of_surjective
    ConnectedComponents.mk ConnectedComponents.continuous_coe ConnectedComponents.surjective_coe
  exact NoetherianSpace.finite

end

end OAI.RepresentationTheory.Satake.NoetherianConnectedComponents.GL.Zariski
