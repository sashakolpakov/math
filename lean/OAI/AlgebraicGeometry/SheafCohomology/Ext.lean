import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-! # Ext -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Ext.Projective

noncomputable section

/-! Functoriality of Ext under isomorphism, used by the ProjectiveCohomology Euler construction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Abelian

universe u v w t

/-- An isomorphism of coefficients induces a linear equivalence on Ext. -/
def extRightIso (R : Type t) [CommRing R]
    {C : Type u} [Category.{v} C] [Abelian C] [Linear R C] [HasExt.{w} C]
    (X : C) {Y Z : C} (e : Y ≅ Z) (n : ℕ) : Ext X Y n ≃ₗ[R] Ext X Z n where
  toFun x := x.comp (Ext.mk₀ e.hom) (Nat.add_zero n)
  invFun x := x.comp (Ext.mk₀ e.inv) (Nat.add_zero n)
  left_inv x := by
    simp only [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      Iso.hom_inv_id, Ext.comp_mk₀_id]
  right_inv x := by
    simp only [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      Iso.inv_hom_id, Ext.comp_mk₀_id]
  map_add' x y := by simp only [Ext.add_comp]
  map_smul' r x := by simp only [Ext.smul_comp, RingHom.id_apply]

end

end OAI.AlgebraicGeometry.SheafCohomology.Ext.Projective
