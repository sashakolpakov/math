import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Sets.Opens

/-! # Preimage Neighborhood -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Finite.PreimageNeighborhood.Constructions

/-! A point in a finite inverse image admits an isolating open inside any prescribed target neighborhood. -/

open _root_.TopologicalSpace

theorem exists_isolating_open {X Y : Type*} [TopologicalSpace X] [T1Space X] [TopologicalSpace Y]
    (f : X → Y) (hf : Continuous f) (T : Set Y) (hT : (f ⁻¹' T).Finite)
    (x : X) (O : Opens Y) (hx : f x ∈ O) :
    ∃ V : Opens X, x ∈ V ∧ Set.MapsTo f (V : Set X) O ∧
      ∀ z ∈ V, f z ∈ T → z = x := by
  let V : Opens X := ⟨f ⁻¹' O ∩ (f ⁻¹' T \ {x})ᶜ,
    (O.isOpen.preimage hf).inter (hT.sdiff (t := {x})).isClosed.isOpen_compl⟩
  refine ⟨V, ⟨hx, fun h => h.2 rfl⟩, fun _ h => h.1, ?_⟩
  intro z hz hzt
  by_contra hne
  exact hz.2 ⟨hzt, hne⟩

end OAI.AlgebraicGeometry.CycleClass.Thom.Finite.PreimageNeighborhood.Constructions
