import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.PointNormalForm

/-! # Neutral Point Normal Form -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.NeutralPointNormalForm.Second

noncomputable section

/-! # Canonical coordinate presentation of second-neutral scheme-valued points -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A X : Over S} [GrpObj X]

/-- A vertically neutral test point is its first coordinate paired with the identity. -/
theorem neutral_normalForm {T : Over S} (a : T ⟶ A ⊗ X) (ha : a ≫ snd A X = 1) :
    ∃ x : T ⟶ A, a = lift x (1 : T ⟶ X) := by
  refine ⟨a ≫ fst A X, ?_⟩
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst]
  · rw [lift_snd]
    exact ha

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.NeutralPointNormalForm.Second
