import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-! # Quotient Relation -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.QuotientRelation.Construction

/-! Equal images under a product quotient are precisely equal quotient
parameters and an unchanged second coordinate. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {A B Q T : C} (f : B ⟶ Q) (x y : T ⟶ B ⊗ A)

theorem productQuotient_first (h : x ≫ (f ⊗ₘ 𝟙 A) = y ≫ (f ⊗ₘ 𝟙 A)) :
    (x ≫ fst B A) ≫ f = (y ≫ fst B A) ≫ f := by
  have he := congrArg (fun z => z ≫ fst Q A) h
  simpa only [Category.assoc, tensorHom_fst] using he

theorem productQuotient_second (h : x ≫ (f ⊗ₘ 𝟙 A) = y ≫ (f ⊗ₘ 𝟙 A)) :
    x ≫ snd B A = y ≫ snd B A := by
  have he := congrArg (fun z => z ≫ snd Q A) h
  simpa only [Category.assoc, tensorHom_snd, Category.comp_id] using he

theorem productQuotient_lift (h : x ≫ (f ⊗ₘ 𝟙 A) = y ≫ (f ⊗ₘ 𝟙 A)) :
    lift (y ≫ fst B A) (x ≫ snd B A) = y := by
  rw [productQuotient_second f x y h]
  simp

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Product.QuotientRelation.Construction
