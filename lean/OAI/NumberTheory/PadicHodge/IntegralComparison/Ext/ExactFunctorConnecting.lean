import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Exact Functor Connecting -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ExactFunctorConnecting

noncomputable section

/-! The original Ext connecting morphisms commute with exact functors, including crystalline restriction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v u' v' z z'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (X : C) {S : ShortComplex C} (hS : S.ShortExact)

theorem connecting (m : ℕ) (α : Ext.{z} X S.X₃ m) :
    (DimensionShift.connecting X hS m α).mapExactFunctor F =
      DimensionShift.connecting (F.obj X) (hS.map_of_exact F) m (α.mapExactFunctor F) := by
  change (α.comp hS.extClass rfl).mapExactFunctor F =
    (α.mapExactFunctor F).comp (hS.map_of_exact F).extClass rfl
  have hδ : (hS.extClass : Ext.{z} S.X₃ S.X₁ 1).mapExactFunctor F =
      ((hS.map_of_exact F).extClass : Ext.{z'} (F.obj S.X₃) (F.obj S.X₁) 1) :=
    Ext.mapExactFunctor_extClass F hS
  exact (Ext.mapExactFunctor_comp F α hS.extClass rfl).trans
    (congrArg (fun e : Ext.{z'} (F.obj S.X₃) (F.obj S.X₁) 1 =>
      (α.mapExactFunctor F).comp e rfl) hδ)

variable (R : Type*) [CommRing R] [Linear R C] [Linear R D] [F.Linear R]

theorem linearEquivalence (m : ℕ)
    [Subsingleton (Ext.{z} X S.X₂ m)] [Subsingleton (Ext.{z} X S.X₂ (m + 1))]
    [Subsingleton (Ext.{z'} (F.obj X) (S.map F).X₂ m)]
    [Subsingleton (Ext.{z'} (F.obj X) (S.map F).X₂ (m + 1))]
    (α : Ext.{z} X S.X₃ m) :
    F.mapExtLinearMap R X S.X₁ (m + 1) (DimensionShift.linearEquivalence X hS m R α) =
      DimensionShift.linearEquivalence (F.obj X) (hS.map_of_exact F) m R
        (F.mapExtLinearMap R X S.X₃ m α) :=
  connecting F X hS m α

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ExactFunctorConnecting
