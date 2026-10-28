import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Affine Neighborhood -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.AffineNeighborhood

/-! A neighborhood on a closed subscheme can be refined by the inverse
image of an actual affine neighborhood in the ambient scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_subopen {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]
    (U : Y.Opens) (W : X.Opens) (x : X) (hxU : f x ∈ U) (hxW : x ∈ W) :
    ∃ (V : Y.Opens), IsAffineOpen V ∧ f x ∈ V ∧ V ≤ U ∧ f ⁻¹ᵁ V ≤ W := by
  obtain ⟨T, hT, hpre⟩ := f.isClosedEmbedding.isInducing.isOpen_iff.mp W.isOpen
  let Z : Y.Opens := ⟨T, hT⟩
  have hxZ : f x ∈ Z := by
    change x ∈ f ⁻¹' T
    rw [hpre]
    exact hxW
  obtain ⟨V, hV, hxV, hVZ⟩ := exists_isAffineOpen_mem_and_subset (show f x ∈ U ⊓ Z from ⟨hxU, hxZ⟩)
  refine ⟨V, hV, hxV, fun y hy => (hVZ hy).1, ?_⟩
  intro y hy
  have hyT : y ∈ f ⁻¹' T := (hVZ hy).2
  rw [hpre] at hyT
  exact hyT

end OAI.NumberTheory.PadicHodge.IntegralComparison.Closed.AffineNeighborhood
