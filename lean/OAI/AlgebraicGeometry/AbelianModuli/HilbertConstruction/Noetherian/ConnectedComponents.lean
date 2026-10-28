import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Connected.Clopen

/-! # Connected Components -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.ConnectedComponents

noncomputable section

/-! A Noetherian space has finitely many open connected components; for schemes these are actual connected open subschemes. -/

open _root_.TopologicalSpace _root_.AlgebraicGeometry

universe u

theorem noetherian_finite_connectedComponents (X : Type u) [TopologicalSpace X] [NoetherianSpace X] :
    Finite (ConnectedComponents X) := by
  have : Finite (irreducibleComponents X) := (NoetherianSpace.finite_irreducibleComponents (α := X)).to_subtype
  let q : (irreducibleComponents X) → ConnectedComponents X :=
    fun Z => ConnectedComponents.mk Z.property.1.1.choose
  apply Finite.of_surjective q
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  refine ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
  apply ConnectedComponents.coe_eq_coe'.mpr
  exact irreducibleComponent_subset_connectedComponent
    (irreducibleComponent_mem_irreducibleComponents x).1.1.choose_spec

theorem connectedComponents_t1 (X : Type u) [TopologicalSpace X] : T1Space (ConnectedComponents X) := by
  constructor
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  apply ConnectedComponents.isQuotientMap_coe.isClosed_preimage.mp
  rw [connectedComponents_preimage_singleton]
  exact isClosed_connectedComponent

theorem noetherian_connectedComponent_open (X : Type u) [TopologicalSpace X] [NoetherianSpace X] (x : X) :
    IsOpen (connectedComponent x) := by
  have := noetherian_finite_connectedComponents X
  have := connectedComponents_t1 X
  exact ConnectedComponents.discreteTopology_iff.mp inferInstance x

def noetherianConnectedComponentOpen (X : Scheme.{u}) [IsNoetherian X] (x : X) : X.Opens :=
  ⟨connectedComponent x, noetherian_connectedComponent_open X x⟩

instance noetherianConnectedComponentOpen_connected (X : Scheme.{u}) [IsNoetherian X] (x : X) :
    ConnectedSpace (noetherianConnectedComponentOpen X x).toScheme :=
  isConnected_iff_connectedSpace.mp isConnected_connectedComponent

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.ConnectedComponents
