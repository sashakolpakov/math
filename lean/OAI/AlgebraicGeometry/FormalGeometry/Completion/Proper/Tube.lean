import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Tube -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.Tube.Construction

noncomputable section

/-!
# Completion: a proper fiber contained in an open stays there on a neighborhood

The complement of the image of the bad locus is open because the projection
is closed. This gives the actual neighborhood needed by product rigidity.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {T Y Z : Scheme.{u}} (p : T ⟶ Y) [UniversallyClosed p]
  (f : T ⟶ Z) (V : Z.Opens)

/-- The largest base open obtained by excluding the image of the complement of the target open. -/
def properTubeOpen : Y.Opens :=
  ⟨(p '' (f ⁻¹' (V : Set Z))ᶜ)ᶜ,
    (p.isClosedMap _ (V.isOpen.preimage f.continuous).isClosed_compl).isOpen_compl⟩

/-- If an entire fiber lies in the target open, its base point lies in this neighborhood. -/
theorem mem_properTubeOpen (y : Y) (hy : ∀ t : T, p t = y → f t ∈ V) :
    y ∈ properTubeOpen p f V := by
  rintro ⟨t, ht, hty⟩
  exact ht (hy t hty)

/-- Above the resulting base neighborhood, the map takes values in the specified target open. -/
theorem properTubeOpen_preimage_le : p ⁻¹ᵁ properTubeOpen p f V ≤ f ⁻¹ᵁ V := by
  intro t ht
  by_contra h
  exact ht ⟨t, h, rfl⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.Tube.Construction
