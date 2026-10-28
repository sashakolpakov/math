import Mathlib.CategoryTheory.Monoidal.Grp

/-! # Group Subobject -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.GroupSubobject.Construction

noncomputable section

/-! Group operations restricted through a monomorphism satisfy the group
axioms, because all their identities can be checked in the ambient group. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory

universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {X A : C} [GrpObj A] (i : X ⟶ A) [Mono i]
  (e : 𝟙_ C ⟶ X) (m : X ⊗ X ⟶ X) (r : X ⟶ X)
  (he : e ≫ i = MonObj.one) (hm : m ≫ i = (i ⊗ₘ i) ≫ MonObj.mul)
  (hr : r ≫ i = i ≫ GrpObj.inv)

@[instance_reducible]
def grpObjOfMono : GrpObj X where
  one := e
  mul := m
  inv := r
  one_mul := by
    apply (cancel_mono i).mp
    simpa only [← tensorHom_id, ← id_tensorHom, Category.assoc,
      tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id, he, hm]
      using congrArg ((𝟙_ C ◁ i) ≫ ·) (MonObj.one_mul A) |>.trans
        (leftUnitor_naturality i)
  mul_one := by
    apply (cancel_mono i).mp
    simpa only [← tensorHom_id, ← id_tensorHom, Category.assoc,
      tensorHom_comp_tensorHom_assoc, Category.id_comp, Category.comp_id, he, hm]
      using congrArg ((i ▷ 𝟙_ C) ≫ ·) (MonObj.mul_one A) |>.trans
        (rightUnitor_naturality i)
  mul_assoc := by
    apply (cancel_mono i).mp
    simpa only [← tensorHom_id, ← id_tensorHom, Category.assoc,
      associator_naturality_assoc, tensorHom_comp_tensorHom_assoc,
      Category.id_comp, Category.comp_id, hm]
      using congrArg (((i ⊗ₘ i) ⊗ₘ i) ≫ ·) (MonObj.mul_assoc A)
  left_inv := by
    apply (cancel_mono i).mp
    simp only [Category.assoc, hm, he, lift_map_assoc, hr, Category.id_comp]
    simpa only [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
      using congrArg (i ≫ ·) (GrpObj.left_inv A)
  right_inv := by
    apply (cancel_mono i).mp
    simp only [Category.assoc, hm, he, lift_map_assoc, hr, Category.id_comp]
    simpa only [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
      using congrArg (i ≫ ·) (GrpObj.right_inv A)

theorem grpObjOfMono_isMonHom :
    letI := grpObjOfMono i e m r he hm hr
    IsMonHom i := by
  let := grpObjOfMono i e m r he hm hr
  exact ⟨he, hm⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.GroupSubobject.Construction
