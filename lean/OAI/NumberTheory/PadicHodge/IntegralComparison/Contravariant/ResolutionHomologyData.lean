import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceZeroKernels
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceZeroCokernel

/-! # Resolution Homology Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionHomologyData

noncomputable section

/-! Actual homology data for applying original contravariant Ext to a source resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (Y : C) (T : ShortComplex Cᵒᵖ)
  {A : Cᵒᵖ} (a : A ⟶ T.X₁) (ha : a ≫ T.toCycles = 0)
  (hS : (ShortComplex.mk a T.toCycles ha).ShortExact)
  [Subsingleton (Ext.{z} T.X₁.unop Y 1)]

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y 0

def data : (T.map F).LeftHomologyData where
  K := (F).obj T.cycles
  H := ModuleCat.of R (Ext.{z} A.unop Y 1)
  i := (F).map T.iCycles
  π := IntegralComparison.Ext.SourceZeroCokernel.connecting R Y hS
  wi := ((F).map_comp T.iCycles T.g).symm.trans
    ((congrArg (F).map T.iCycles_g).trans ((F).map_zero _ _))
  hi := IntegralComparison.Ext.SourceZeroKernels.cycleKernel R Y T
  wπ :=
    (congrArg (fun g => g ≫ IntegralComparison.Ext.SourceZeroCokernel.connecting R Y hS)
      (IntegralComparison.Ext.SourceZeroKernels.cycleKernel_lift R Y T)).trans (IntegralComparison.Ext.SourceZeroCokernel.condition R Y hS)
  hπ := CokernelCofork.isColimitOfIsColimitOfIff' (IntegralComparison.Ext.SourceZeroCokernel.isCokernel R Y hS) _
    (fun {_} φ => (congrArg (fun g => g ≫ φ = 0) (IntegralComparison.Ext.SourceZeroKernels.cycleKernel_lift R Y T).symm).to_iff)

def homologyIso : (T.map F).homology ≅ ModuleCat.of R (Ext.{z} A.unop Y 1) :=
  (data R Y T a ha hS).homologyIso

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionHomologyData
