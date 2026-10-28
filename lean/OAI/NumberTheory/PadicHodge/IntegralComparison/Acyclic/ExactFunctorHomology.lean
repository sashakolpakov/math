import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ExactFunctorModule
import OAI.NumberTheory.PadicHodge.IntegralComparison.ShortCyclesExactFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.MappedSequenceConnecting

/-! # Exact Functor Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ExactFunctorHomology

noncomputable section

/-! The actual acyclic-resolution homology data commute with exact functors and cycle transport. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R] (X : C)
  {T : ShortComplex C} {U : ShortComplex D} (φ : T.map F ⟶ U)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 0
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R (F.obj X) 0

def shortMap : T.map G ⟶ U.map H :=
  IntegralComparison.Ext.ExactFunctorModule.shortMap F R X 0 T ≫ (H).mapShortComplex.map φ

theorem shortMap_id : shortMap F R X (𝟙 (T.map F)) = IntegralComparison.Ext.ExactFunctorModule.shortMap F R X 0 T := by
  exact (congrArg (fun h => IntegralComparison.Ext.ExactFunctorModule.shortMap F R X 0 T ≫ h)
    ((H).mapShortComplex.map_id (T.map F))).trans (Category.comp_id _)

variable {A : C} {B : D} (a : A ⟶ T.X₁) (b : B ⟶ U.X₁)
  (ha : a ≫ T.toCycles = 0) (hb : b ≫ U.toCycles = 0)
  (hT : (ShortComplex.mk a T.toCycles ha).ShortExact)
  (hU : (ShortComplex.mk b U.toCycles hb).ShortExact)
  [Subsingleton (Ext.{z} X T.X₁ 1)] [Subsingleton (Ext.{z} (F.obj X) U.X₁ 1)]
  (g : F.obj A ⟶ B) (hg : g ≫ b = F.map a ≫ φ.τ₁)

local notation "dT" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.data R X T a ha hT
local notation "dU" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.data R (F.obj X) U b hb hU
local notation "c" => OAI.NumberTheory.PadicHodge.IntegralComparison.ShortCyclesExactFunctor.cycleMap F φ
local notation "η" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ExactFunctorModule.component F R X 0

omit [Subsingleton (Ext.{z} X T.X₁ 1)] [Subsingleton (Ext.{z} (F.obj X) U.X₁ 1)] in
private theorem commi : (η T.cycles ≫ (H).map c) ≫ (H).map U.iCycles =
    (G).map T.iCycles ≫ (η T.X₂ ≫ (H).map φ.τ₂) := by
  calc
    _ = η T.cycles ≫ (H).map (c ≫ U.iCycles) := by rw [Category.assoc, ← (H).map_comp]
    _ = η T.cycles ≫ (H).map (F.map T.iCycles ≫ φ.τ₂) := by rw [ShortCyclesExactFunctor.cycleMap_i]
    _ = (η T.cycles ≫ (H).map (F.map T.iCycles)) ≫ (H).map φ.τ₂ :=
      (congrArg (fun h => η T.cycles ≫ h) ((H).map_comp (F.map T.iCycles) φ.τ₂)).trans
        (Category.assoc _ _ _).symm
    _ = _ := by rw [← IntegralComparison.Ext.ExactFunctorModule.naturality, Category.assoc]

omit [Subsingleton (Ext.{z} X T.X₁ 1)] [Subsingleton (Ext.{z} (F.obj X) U.X₁ 1)] in
private theorem commf : (G).map T.toCycles ≫ (η T.cycles ≫ (H).map c) =
    (η T.X₁ ≫ (H).map φ.τ₁) ≫ (H).map U.toCycles := by
  calc
    _ = ((G).map T.toCycles ≫ η T.cycles) ≫ (H).map c := (Category.assoc _ _ _).symm
    _ = (η T.X₁ ≫ (H).map (F.map T.toCycles)) ≫ (H).map c := by rw [IntegralComparison.Ext.ExactFunctorModule.naturality]
    _ = η T.X₁ ≫ (H).map (F.map T.toCycles ≫ c) := by rw [Category.assoc, ← (H).map_comp]
    _ = η T.X₁ ≫ (H).map (φ.τ₁ ≫ U.toCycles) :=
      congrArg (fun h => η T.X₁ ≫ (H).map h) (ShortCyclesExactFunctor.toCycles F φ)
    _ = _ := (congrArg (fun h => η T.X₁ ≫ h) ((H).map_comp φ.τ₁ U.toCycles)).trans
      (Category.assoc _ _ _).symm

def data : ShortComplex.LeftHomologyMapData (shortMap F R X φ) dT dU where
  φK := η T.cycles ≫ (H).map c
  φH := IntegralComparison.Ext.ExactFunctorModule.component F R X 1 A ≫
    (IntegralComparison.Ext.ModuleFunctor.functor R (F.obj X) 1).map g
  commi := ExactFunctorHomology.commi F R X φ
  commf' := by
    have hs : (dT).f' = (G).map T.toCycles := IntegralComparison.Ext.ZeroKernels.cycleKernel_lift R X T
    have ht : (dU).f' = (H).map U.toCycles := IntegralComparison.Ext.ZeroKernels.cycleKernel_lift R (F.obj X) U
    exact (congrArg (fun f => f ≫ (η T.cycles ≫ (H).map c)) hs).trans
      ((commf F R X φ).trans (congrArg (fun f => (η T.X₁ ≫ (H).map φ.τ₁) ≫ f) ht.symm))
  commπ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    exact (IntegralComparison.Ext.MappedSequenceConnecting.connecting F X hT hU
      (ShortCyclesExactFunctor.sequenceMap F φ a b ha hb g hg) 0 α).symm

include hg in
theorem homology : ShortComplex.homologyMap (shortMap F R X φ) ≫ (dU).homologyIso.hom =
    (dT).homologyIso.hom ≫ (IntegralComparison.Ext.ExactFunctorModule.component F R X 1 A ≫
      (IntegralComparison.Ext.ModuleFunctor.functor R (F.obj X) 1).map g) :=
  (data F R X φ a b ha hb hT hU g hg).homologyMap_comm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ExactFunctorHomology
