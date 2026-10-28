import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceExactFunctorConnecting
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceConnectingNaturality

/-! # Source Mapped Sequence Connecting -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceMappedSequenceConnecting

noncomputable section

/-! Original source connecting maps remain compatible with exact restriction and cycle sequence transport. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

attribute [local instance] preservesFiniteLimits_op preservesFiniteColimits_op

open Abelian

universe u v u' v' z z'

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (Y : C) {S : ShortComplex Cᵒᵖ} (hS : S.ShortExact)
  {T : ShortComplex Dᵒᵖ} (hT : T.ShortExact) (φ : S.map F.op ⟶ T)

theorem connecting (m : ℕ) (α : Ext.{z} S.X₃.unop Y m) :
    SourceDimensionShift.connecting hT.unop (F.obj Y) m
      ((Ext.mk₀ φ.τ₃.unop).precomp (F.obj Y) (zero_add m) (α.mapExactFunctor F)) =
    (Ext.mk₀ φ.τ₁.unop).precomp (F.obj Y) (zero_add (m + 1))
      ((SourceDimensionShift.connecting hS.unop Y m α).mapExactFunctor F) :=
  (SourceConnectingNaturality.connecting (F.obj Y) (hS.map_of_exact F.op) hT φ m (α.mapExactFunctor F)).trans
    (congrArg ((Ext.mk₀ φ.τ₁.unop).precomp (F.obj Y) (zero_add (m + 1)))
      (SourceExactFunctorConnecting.connecting F Y hS.unop m α).symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceMappedSequenceConnecting
