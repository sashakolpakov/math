import OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.PointNormalForm

/-! # Point Normal Form -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.PointNormalForm

noncomputable section

/-!
# Every actual neutral-axis test point has its canonical coordinate presentation
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

variable {S : Scheme.{u}} {A X : Over S} [GrpObj A]

/-- A horizontally neutral point is precisely a lift of the identity and its second coordinate. -/
theorem neutral_normalForm {T : Over S} (a : T ⟶ A ⊗ X) (ha : a ≫ fst A X = 1) :
    ∃ z : T ⟶ X, a = lift (1 : T ⟶ A) z := by
  refine ⟨a ≫ snd A X, ?_⟩
  apply CartesianMonoidalCategory.hom_ext
  · rw [lift_fst]
    exact ha
  · rw [lift_snd]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Neutral.PointNormalForm
