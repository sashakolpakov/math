import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Shear Isomorphisms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.ShearIsomorphisms

noncomputable section

/-! Explicit interchange and integer shear automorphisms of the square of
a group object. -/
open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj
universe u v
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

def productSwapIso (A : C) : A ⊗ A ≅ A ⊗ A where
  hom := lift (snd A A) (fst A A)
  inv := lift (snd A A) (fst A A)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext <;> simp

@[reassoc (attr := simp)]
theorem productSwapIso_hom_fst (A : C) : (productSwapIso A).hom ≫ fst A A = snd A A := by
  simp [productSwapIso]

@[reassoc (attr := simp)]
theorem productSwapIso_hom_snd (A : C) : (productSwapIso A).hom ≫ snd A A = fst A A := by
  simp [productSwapIso]

def productShearIso (A : C) [GrpObj A] (t : ℤ) : A ⊗ A ≅ A ⊗ A where
  hom := lift (fst A A * snd A A ^ t) (snd A A)
  inv := lift (fst A A * (snd A A ^ t)⁻¹) (snd A A)
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [MonObj.comp_mul, GrpObj.comp_inv, GrpObj.comp_zpow]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp [MonObj.comp_mul, GrpObj.comp_zpow]

@[reassoc (attr := simp)]
theorem productShearIso_hom_fst (A : C) [GrpObj A] (t : ℤ) :
    (productShearIso A t).hom ≫ fst A A = fst A A * snd A A ^ t := by
  simp [productShearIso]

@[reassoc (attr := simp)]
theorem productShearIso_hom_snd (A : C) [GrpObj A] (t : ℤ) :
    (productShearIso A t).hom ≫ snd A A = snd A A := by
  simp [productShearIso]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.ShearIsomorphisms
