import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Neighborhood Pullback -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.NeighborhoodPullback

/-! Affine neighborhoods of finite sets pull back along an affine morphism. -/

open _root_.AlgebraicGeometry

theorem finite_set_affine_neighborhood_of_affine {X Y : Scheme.{0}}
    (f : X ⟶ Y) [IsAffineHom f]
    (hY : ∀ F : Set Y, F.Finite → ∃ V : Y.Opens, IsAffineOpen V ∧ F ⊆ V)
    (F : Set X) (hF : F.Finite) : ∃ V : X.Opens, IsAffineOpen V ∧ F ⊆ V := by
  obtain ⟨V, hV, hFV⟩ := hY (f '' F) (hF.image f)
  exact ⟨f ⁻¹ᵁ V, hV.preimage f, fun x hx => hFV ⟨x, hx, rfl⟩⟩

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Affine.NeighborhoodPullback
