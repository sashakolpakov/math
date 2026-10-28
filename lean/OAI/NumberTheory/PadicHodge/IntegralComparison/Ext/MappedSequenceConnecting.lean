import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ExactFunctorConnecting
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ConnectingNaturality

/-! # Mapped Sequence Connecting -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.MappedSequenceConnecting

noncomputable section

/-! Connecting morphisms remain compatible after exact restriction and canonical comparison of cycle sequences. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v u' v' z z'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (X : C) {S : ShortComplex C} (hS : S.ShortExact)
  {T : ShortComplex D} (hT : T.ShortExact) (φ : S.map F ⟶ T)

theorem connecting (m : ℕ) (α : Ext.{z} X S.X₃ m) :
    DimensionShift.connecting (F.obj X) hT m
      ((Ext.mk₀ φ.τ₃).postcomp (F.obj X) (add_zero m) (α.mapExactFunctor F)) =
    (Ext.mk₀ φ.τ₁).postcomp (F.obj X) (add_zero (m + 1))
      ((DimensionShift.connecting X hS m α).mapExactFunctor F) :=
  (ConnectingNaturality.connecting (F.obj X) (hS.map_of_exact F) hT φ m (α.mapExactFunctor F)).trans
    (congrArg ((Ext.mk₀ φ.τ₁).postcomp (F.obj X) (add_zero (m + 1)))
      (ExactFunctorConnecting.connecting F X hS m α).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.MappedSequenceConnecting
