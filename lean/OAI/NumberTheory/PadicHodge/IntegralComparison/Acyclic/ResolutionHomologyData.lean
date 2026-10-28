import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroKernels
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroCokernel

/-! # Resolution Homology Data -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData

noncomputable section

/-!
# IntegralComparison: actual homology data for sections of an acyclic resolution
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (X : C) (T : ShortComplex C)
  {A : C} (a : A ⟶ T.X₁) (ha : a ≫ T.toCycles = 0)
  (hS : (ShortComplex.mk a T.toCycles ha).ShortExact)
  [Subsingleton (Ext.{z} X T.X₁ 1)]

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 0

def data : (T.map F).LeftHomologyData where
  K := (F).obj T.cycles
  H := ModuleCat.of R (Ext.{z} X A 1)
  i := (F).map T.iCycles
  π := IntegralComparison.Ext.ZeroCokernel.connecting R X hS
  wi := ((F).map_comp T.iCycles T.g).symm.trans
    ((congrArg (F).map T.iCycles_g).trans ((F).map_zero _ _))
  hi := IntegralComparison.Ext.ZeroKernels.cycleKernel R X T
  wπ := by
    exact (congrArg (fun g => g ≫ IntegralComparison.Ext.ZeroCokernel.connecting R X hS)
      (IntegralComparison.Ext.ZeroKernels.cycleKernel_lift R X T)).trans (IntegralComparison.Ext.ZeroCokernel.condition R X hS)
  hπ := by
    exact CokernelCofork.isColimitOfIsColimitOfIff' (IntegralComparison.Ext.ZeroCokernel.isCokernel R X hS) _
      (fun {_} φ => (congrArg (fun g => g ≫ φ = 0) (IntegralComparison.Ext.ZeroKernels.cycleKernel_lift R X T).symm).to_iff)

def homologyIso : (T.map F).homology ≅ ModuleCat.of R (Ext.{z} X A 1) :=
  (data R X T a ha hS).homologyIso

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData
