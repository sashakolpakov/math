import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceDimensionShift
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Source Exact Functor Connecting -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceExactFunctorConnecting

noncomputable section

/-! Original source Ext connecting maps commute with exact functors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v u' v' z z'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (Y : C) {S : ShortComplex C} (hS : S.ShortExact)

theorem connecting (m : ℕ) (α : Ext.{z} S.X₁ Y m) :
    (SourceDimensionShift.connecting hS Y m α).mapExactFunctor F =
      SourceDimensionShift.connecting (hS.map_of_exact F) (F.obj Y) m (α.mapExactFunctor F) := by
  change (hS.extClass.comp α (Nat.add_comm 1 m)).mapExactFunctor F =
    (hS.map_of_exact F).extClass.comp (α.mapExactFunctor F) (Nat.add_comm 1 m)
  have hδ : (hS.extClass : Ext.{z} S.X₃ S.X₁ 1).mapExactFunctor F =
      ((hS.map_of_exact F).extClass : Ext.{z'} (F.obj S.X₃) (F.obj S.X₁) 1) :=
    Ext.mapExactFunctor_extClass F hS
  exact (Ext.mapExactFunctor_comp F hS.extClass α (Nat.add_comm 1 m)).trans
    (congrArg (fun e : Ext.{z'} (F.obj S.X₃) (F.obj S.X₁) 1 =>
      e.comp (α.mapExactFunctor F) (Nat.add_comm 1 m)) hδ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceExactFunctorConnecting
