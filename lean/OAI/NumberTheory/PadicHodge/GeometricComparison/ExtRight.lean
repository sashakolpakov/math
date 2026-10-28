import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-! # Ext Right -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ExtRight.ExtRightIsoLinear

noncomputable section

/-! Isomorphisms of coefficient objects give linear equivalences on actual Ext groups. -/

open _root_.CategoryTheory

universe u v w

variable (R : Type*) [CommRing R] {C : Type u} [Category.{v} C] [Abelian C]
  [Linear R C] [HasExt.{w} C]

def equiv (A : C) {M N : C} (e : M ≅ N) (n : ℕ) :
    Abelian.Ext.{w} A M n ≃ₗ[R] Abelian.Ext.{w} A N n := by
  let := HasDerivedCategory.standard C
  exact Abelian.Ext.homLinearEquiv.trans
    ((Linear.homCongr R (Iso.refl ((DerivedCategory.singleFunctor C 0).obj A))
      ((shiftFunctor (DerivedCategory C) (n : ℤ)).mapIso
        ((DerivedCategory.singleFunctor C 0).mapIso e))).trans Abelian.Ext.homLinearEquiv.symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ExtRight.ExtRightIsoLinear
