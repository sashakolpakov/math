import Mathlib.Topology.LocalAtTarget

/-! # Map Open Cover -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Proper.MapOpenCover.Constructions

/-! Properness of a continuous map is local on an open cover of its target. -/

open _root_.TopologicalSpace _root_.Topology Set

theorem isProperMap_of_openCover {X Y ι : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} {U : ι → Opens Y} (hU : IsOpenCover U) (hf : Continuous f)
    (h : ∀ i, IsProperMap ((U i : Set Y).restrictPreimage f)) : IsProperMap f := by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨hf, hU.isClosedMap_iff_restrictPreimage.mpr (fun i => (h i).isClosedMap), ?_⟩
  intro y
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp
    (show y ∈ iSup U by rw [hU.iSup_eq_top]; trivial)
  have hc := (h i).isCompact_preimage (isCompact_singleton (x := (⟨y, hi⟩ : U i)))
  have hh := hc.image continuous_subtype_val
  rw [image_val_preimage_restrictPreimage, Set.image_singleton] at hh
  exact hh

end OAI.AlgebraicGeometry.CycleClass.Thom.Proper.MapOpenCover.Constructions
