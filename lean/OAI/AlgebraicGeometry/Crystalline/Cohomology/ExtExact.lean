import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ConnectingNaturality
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Ext Exact -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.ExtExact.ExtExactFunctorConnecting

noncomputable section

/-! # Exact functors preserve the original Ext connecting maps -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open _root_.CategoryTheory.Abelian

universe u v z u' v' z'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (X : C) {S : ShortComplex C} {T : ShortComplex D}
  (hS : S.ShortExact) (hT : T.ShortExact) (φ : S.map F ⟶ T)

theorem connecting (m : ℕ) (α : Ext.{z} X S.X₃ m) :
    NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift.connecting (F.obj X) hT m
      ((Ext.mk₀ φ.τ₃).postcomp (F.obj X) (add_zero m) (α.mapExactFunctor F)) =
    (Ext.mk₀ φ.τ₁).postcomp (F.obj X) (add_zero (m + 1))
      ((NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift.connecting X hS m α).mapExactFunctor F) := by
  have h := NumberTheory.PadicHodge.IntegralComparison.Ext.ConnectingNaturality.connecting (F.obj X) (hS.map_of_exact F) hT φ m
    (α.mapExactFunctor F)
  change _ = (Ext.mk₀ φ.τ₁).postcomp (F.obj X) (add_zero (m + 1))
    ((α.comp hS.extClass rfl).mapExactFunctor F)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact h

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.ExtExact.ExtExactFunctorConnecting
