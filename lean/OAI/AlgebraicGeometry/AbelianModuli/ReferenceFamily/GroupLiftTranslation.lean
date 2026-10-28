import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Group Lift Translation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupLiftTranslation

/-! Translating a lift by a chosen reference lift identifies its fiber
with the identity fiber. This is natural in the source and uses the
actual group operation on morphisms. -/

open _root_.CategoryTheory
open scoped _root_.CategoryTheory.MonObj

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]
    {S T A : C} [GrpObj A] (r : S ⟶ T) (c : T ⟶ A)

def groupLiftIdentityEquiv : {f : T ⟶ A // r ≫ f = r ≫ c} ≃ {f : T ⟶ A // r ≫ f = 1} where
  toFun f := ⟨f.val / c, by rw [GrpObj.comp_div, f.property]; exact div_self' _⟩
  invFun f := ⟨f.val * c, by rw [MonObj.comp_mul, f.property, one_mul]⟩
  left_inv f := Subtype.ext (div_mul_cancel _ _)
  right_inv f := Subtype.ext (mul_div_cancel_right _ _)

theorem groupLiftIdentityEquiv_natural {S' T' : C} (r' : S' ⟶ T')
    (a : S' ⟶ S) (b : T' ⟶ T) (h : r' ≫ b = a ≫ r)
    (f : {f : T ⟶ A // r ≫ f = r ≫ c}) :
    b ≫ (groupLiftIdentityEquiv r c f).val =
      (groupLiftIdentityEquiv r' (b ≫ c)
        ⟨b ≫ f.val, by
          calc
            r' ≫ (b ≫ f.val) = a ≫ (r ≫ f.val) := by rw [← Category.assoc, h, Category.assoc]
            _ = a ≫ (r ≫ c) := congrArg (fun z => a ≫ z) f.property
            _ = r' ≫ (b ≫ c) := by rw [← Category.assoc, ← h, Category.assoc]⟩).val :=
  GrpObj.comp_div b f.val c

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GroupLiftTranslation
