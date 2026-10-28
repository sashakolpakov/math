import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Sets.Opens

/-! # Graph Local Bound -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Proper.GraphLocalBound.Constructions

/-! Properness gives an actual compact coordinate bound over an open base neighborhood. -/

open _root_.TopologicalSpace
open scoped _root_.Topology

theorem exists_local_compact_bound {X N F : Type*} [TopologicalSpace X] [TopologicalSpace N]
    [TopologicalSpace F] [WeaklyLocallyCompactSpace N]
    (g : X → N) (hg : IsProperMap g) (e : X → F) (he : Continuous e) (x : N) :
    ∃ (U : Opens N) (K : Set F), x ∈ U ∧ IsCompact K ∧
      ∀ y : X, g y ∈ U → e y ∈ K := by
  obtain ⟨C, hC, hxC⟩ := exists_compact_mem_nhds x
  refine ⟨⟨interior C, isOpen_interior⟩, e '' (g ⁻¹' C), mem_interior_iff_mem_nhds.mpr hxC,
    (hg.isCompact_preimage hC).image he, ?_⟩
  intro y hy
  exact ⟨y, (show g y ∈ C from interior_subset hy), rfl⟩

end OAI.AlgebraicGeometry.CycleClass.Thom.Proper.GraphLocalBound.Constructions
