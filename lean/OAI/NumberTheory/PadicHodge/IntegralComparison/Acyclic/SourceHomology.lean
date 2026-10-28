import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceModule
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData

/-! # Source Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.SourceHomology

noncomputable section

/-! The native acyclic-resolution homology calculation respects precomposition in the source of Ext. -/

open _root_.CategoryTheory

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] {X X' : C} (f : X' ⟶ X)
  (T : ShortComplex C) {A : C} (a : A ⟶ T.X₁) (ha : a ≫ T.toCycles = 0)
  (hT : (ShortComplex.mk a T.toCycles ha).ShortExact)
  [Subsingleton (Ext.{z} X T.X₁ 1)] [Subsingleton (Ext.{z} X' T.X₁ 1)]

local notation "d" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.data R X T a ha hT
local notation "d'" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.data R X' T a ha hT

def data : ShortComplex.LeftHomologyMapData (IntegralComparison.Ext.SourceModule.shortMap R f 0 T) d d' where
  φK := IntegralComparison.Ext.SourceModule.component R f 0 T.cycles
  φH := IntegralComparison.Ext.SourceModule.component R f 1 A
  commi := (IntegralComparison.Ext.SourceModule.naturality R f 0 T.iCycles).symm
  commf' := by
    have hs : (d).f' = (IntegralComparison.Ext.ModuleFunctor.functor R X 0).map T.toCycles :=
      IntegralComparison.Ext.ZeroKernels.cycleKernel_lift R X T
    have ht : (d').f' = (IntegralComparison.Ext.ModuleFunctor.functor R X' 0).map T.toCycles :=
      IntegralComparison.Ext.ZeroKernels.cycleKernel_lift R X' T
    exact (congrArg (fun g => g ≫ IntegralComparison.Ext.SourceModule.component R f 0 T.cycles) hs).trans
      ((IntegralComparison.Ext.SourceModule.naturality R f 0 T.toCycles).trans
        (congrArg (fun g => IntegralComparison.Ext.SourceModule.component R f 0 T.X₁ ≫ g) ht.symm))
  commπ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    exact (IntegralComparison.Ext.SourceModule.connecting R f hT 0 α).symm

theorem homology : ShortComplex.homologyMap (IntegralComparison.Ext.SourceModule.shortMap R f 0 T) ≫ (d').homologyIso.hom =
    (d).homologyIso.hom ≫ IntegralComparison.Ext.SourceModule.component R f 1 A :=
  (data R f T a ha hT).homologyMap_comm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.SourceHomology
