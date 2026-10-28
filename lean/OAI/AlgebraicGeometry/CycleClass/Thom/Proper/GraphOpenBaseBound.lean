import OAI.AlgebraicGeometry.CycleClass.Thom.Proper.GraphLocalBound
import Mathlib.Topology.Maps.Basic

/-! # Graph Open Base Bound -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Proper.GraphOpenBaseBound.Constructions

/-! A proper map into an actual open subspace has a compact coordinate bound on an open neighborhood in the original ambient space. -/

open _root_.TopologicalSpace

theorem exists_ambient_local_compact_bound {X Y N F : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace N] [TopologicalSpace F]
    [WeaklyLocallyCompactSpace Y] (g : X → Y) (hg : IsProperMap g)
    (j : Y → N) (hj : Topology.IsOpenEmbedding j) (e : X → F) (he : Continuous e) (x : Y) :
    ∃ (U : Opens N) (K : Set F), j x ∈ U ∧ (U : Set N) ⊆ Set.range j ∧ IsCompact K ∧
      ∀ y : X, j (g y) ∈ U → e y ∈ K := by
  obtain ⟨A, K, hx, hK, hb⟩ := GraphLocalBound.Constructions.exists_local_compact_bound g hg e he x
  refine ⟨⟨j '' (A : Set Y), hj.isOpenMap _ A.isOpen⟩, K, ⟨x, hx, rfl⟩,
    Set.image_subset_range _ _, hK, ?_⟩
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hy
  exact hb y ((hj.injective hzy) ▸ hz)

end OAI.AlgebraicGeometry.CycleClass.Thom.Proper.GraphOpenBaseBound.Constructions
