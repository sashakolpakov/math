import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.EffectiveEpi.Basic

/-! # Group Operations Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupOperationsIs.Construction.GroupOperations

/-!
# Group laws for descended operations

The group laws can be verified after the epimorphic quotient maps on the
source and its third power. This file does not assume a group structure on
the quotient object.
-/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {A B : C} [GrpObj A] (q : A ⟶ B) (m : B ⊗ B ⟶ B)
    (hm : (q ⊗ₘ q) ≫ m = MonObj.mul ≫ q)

include hm in
/-- Compatibility of multiplication can be used on arbitrary source-valued
points, before the target has been given a group structure. -/
theorem lift_mul {T : C} (a b : T ⟶ A) :
    lift (a ≫ q) (b ≫ q) ≫ m = (a * b) ≫ q := by
  rw [← lift_map, Category.assoc, hm, ← Category.assoc]
  rfl

variable [Epi q]

include hm in
theorem left_unit :
    lift (toUnit B ≫ MonObj.one ≫ q) (𝟙 B) ≫ m = 𝟙 B := by
  apply (cancel_epi q).mp
  rw [comp_lift_assoc]
  have h := lift_mul q m hm (1 : A ⟶ A) (𝟙 A)
  rw [one_mul, Category.id_comp] at h
  simpa [Hom.one_def, Category.assoc] using h

include hm in
theorem right_unit :
    lift (𝟙 B) (toUnit B ≫ MonObj.one ≫ q) ≫ m = 𝟙 B := by
  apply (cancel_epi q).mp
  rw [comp_lift_assoc]
  have h := lift_mul q m hm (𝟙 A) (1 : A ⟶ A)
  rw [mul_one, Category.id_comp] at h
  simpa [Hom.one_def, Category.assoc] using h

include hm in
omit [Epi q] in
theorem associative [Epi ((q ⊗ₘ q) ⊗ₘ q)] :
    m ▷ B ≫ m = (α_ B B B).hom ≫ B ◁ m ≫ m := by
  apply (cancel_epi ((q ⊗ₘ q) ⊗ₘ q)).mp
  let a : (A ⊗ A) ⊗ A ⟶ A := fst (A ⊗ A) A ≫ fst A A
  let b : (A ⊗ A) ⊗ A ⟶ A := fst (A ⊗ A) A ≫ snd A A
  let c : (A ⊗ A) ⊗ A ⟶ A := snd (A ⊗ A) A
  have heq : ((q ⊗ₘ q) ⊗ₘ q) = lift (lift (a ≫ q) (b ≫ q)) (c ≫ q) := by
    apply hom_ext
    · apply hom_ext <;> simp [a, b]
    · simp [c]
  rw [heq, lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc,
    lift_mul q m hm a b, lift_mul q m hm b c,
    lift_mul q m hm (a * b) c, lift_mul q m hm a (b * c), mul_assoc]

/-- Operations compatible with an epimorphic map from a group satisfy the
group axioms. Associativity is checked after the epimorphism on third powers. -/
@[instance_reducible]
def group [Epi ((q ⊗ₘ q) ⊗ₘ q)] (invB : B ⟶ B)
    (hi : q ≫ invB = GrpObj.inv ≫ q) : GrpObj B where
  one := MonObj.one ≫ q
  mul := m
  inv := invB
  one_mul := by
    apply (cancel_epi (λ_ B).inv).mp
    have h : (λ_ B).inv ≫ (MonObj.one ≫ q) ▷ B =
        lift (toUnit B ≫ MonObj.one ≫ q) (𝟙 B) := by
      apply hom_ext <;> simp
    rw [← Category.assoc, h, left_unit q m hm, Iso.inv_hom_id]
  mul_one := by
    apply (cancel_epi (ρ_ B).inv).mp
    have h : (ρ_ B).inv ≫ B ◁ (MonObj.one ≫ q) =
        lift (𝟙 B) (toUnit B ≫ MonObj.one ≫ q) := by
      apply hom_ext <;> simp
    rw [← Category.assoc, h, right_unit q m hm, Iso.inv_hom_id]
  mul_assoc := associative q m hm
  left_inv := by
    apply (cancel_epi q).mp
    rw [comp_lift_assoc]
    have h := lift_mul q m hm ((𝟙 A)⁻¹) (𝟙 A)
    rw [inv_mul_cancel] at h
    simpa [Hom.inv_def, Hom.one_def, hi, Category.assoc] using h

  right_inv := by
    apply (cancel_epi q).mp
    rw [comp_lift_assoc]
    have h := lift_mul q m hm (𝟙 A) ((𝟙 A)⁻¹)
    rw [mul_inv_cancel] at h
    simpa [Hom.inv_def, Hom.one_def, hi, Category.assoc] using h

/-- The map used to descend the operations is a group homomorphism for the
constructed target group structure. -/
theorem isMonHom_group [Epi ((q ⊗ₘ q) ⊗ₘ q)] (invB : B ⟶ B)
    (hi : q ≫ invB = GrpObj.inv ≫ q) :
    let := group q m hm invB hi
    IsMonHom q := by
  let := group q m hm invB hi
  exact ⟨rfl, hm.symm⟩

/-- Commutativity descends after checking on the epimorphic square of the
quotient map. -/
theorem isCommMonObj_group [BraidedCategory C] [IsCommMonObj A]
    [Epi (q ⊗ₘ q)] [Epi ((q ⊗ₘ q) ⊗ₘ q)] (invB : B ⟶ B)
    (hi : q ≫ invB = GrpObj.inv ≫ q) :
    let := group q m hm invB hi
    IsCommMonObj B := by
  let := group q m hm invB hi
  constructor
  change (β_ B B).hom ≫ m = m
  apply (cancel_epi (q ⊗ₘ q)).mp
  rw [← lift_fst_comp_snd_comp q q, lift_braiding_hom_assoc,
    lift_mul q m hm, lift_mul q m hm, mul_comm]

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.GroupOperationsIs.Construction.GroupOperations
