import OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

/-! # Point Normal Form -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.PointNormalForm

noncomputable section

/-!
# Actual product points admit canonical common-coordinate presentations
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {S : Scheme.{u}} {A X : Over S} [GrpObj A]

/-- Three actual horizontal product points are lifts of two group coordinates and one common fixed coordinate. -/
theorem product_normalForm {T : Over S} (a b c : T ⟶ A ⊗ X)
    (h : FiberwiseMultiplication.ProductRel (fst A X) (snd A X) a b c) :
    ∃ (x y : T ⟶ A) (z : T ⟶ X), a = lift x z ∧ b = lift y z ∧ c = lift (x * y) z := by
  refine ⟨a ≫ fst A X, b ≫ fst A X, a ≫ snd A X, (lift_comp_fst_snd a).symm, ?_, ?_⟩
  · apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
    · rw [lift_snd]
      exact h.2.1.symm
  · apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      exact h.1.symm
    · rw [lift_snd]
      exact h.2.2.symm

variable {B Y : Over S} (f : A ⟶ B) (g : X ⟶ Y)

omit [GrpObj A] in
/-- Equality in the product quotient detects equality of the first group-coordinate quotient images. -/
theorem images_fst {T : Over S} (x u : T ⟶ A) (z w : T ⟶ X)
    (h : lift x z ≫ (f ⊗ₘ g) = lift u w ≫ (f ⊗ₘ g)) : x ≫ f = u ≫ f := by
  simpa using congrArg (fun a => a ≫ fst B Y) h

omit [GrpObj A] in
/-- Equality in the product quotient also detects equality of the second coordinate images. -/
theorem images_snd {T : Over S} (x u : T ⟶ A) (z w : T ⟶ X)
    (h : lift x z ≫ (f ⊗ₘ g) = lift u w ≫ (f ⊗ₘ g)) : z ≫ g = w ≫ g := by
  simpa using congrArg (fun a => a ≫ snd B Y) h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Product.PointNormalForm
