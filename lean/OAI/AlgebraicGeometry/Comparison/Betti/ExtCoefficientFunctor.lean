import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Ext Coefficient Functor -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ExtCoefficientFunctor

noncomputable section

/-! The derived formula for exact inverse image with source and target coefficient maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Abelian

universe w w' u u' v v'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] [HasExt.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D] [HasExt.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X Y : C} {X' Y' : D} (s : X' ⟶ F.obj X) (t : F.obj Y ⟶ Y')

theorem exactFunctorCoefficientHom (n : ℕ) (a : Ext.{w} X Y n) :
    ((Ext.mk₀ s).comp ((a.mapExactFunctor F).comp (Ext.mk₀ t) (add_zero n)) (zero_add n)).hom =
      (DerivedCategory.singleFunctor D 0).map s ≫
        ((F.mapDerivedCategorySingleFunctor 0).inv.app X ≫ ShiftedHom.map a.hom F.mapDerivedCategory ≫
          ((F.mapDerivedCategorySingleFunctor 0).hom.app Y)⟦(n : ℤ)⟧') ≫
        ((DerivedCategory.singleFunctor D 0).map t)⟦(n : ℤ)⟧' := by
  rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp, Ext.comp_hom,
    Ext.mk₀_hom, ShiftedHom.comp_mk₀, Ext.mapExactFunctor_hom]

end

end OAI.AlgebraicGeometry.Comparison.Betti.ExtCoefficientFunctor
