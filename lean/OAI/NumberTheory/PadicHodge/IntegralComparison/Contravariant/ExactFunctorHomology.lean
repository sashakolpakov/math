import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionHomologyData
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceExactFunctorModule
import OAI.NumberTheory.PadicHodge.IntegralComparison.ShortCyclesExactFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceMappedSequenceConnecting

/-! # Exact Functor Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ExactFunctorHomology

noncomputable section

/-! The actual acyclic source-resolution homology data commute with exact functors and cycle transport. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

attribute [local instance] preservesFiniteLimits_op preservesFiniteColimits_op

open Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R] (Y : C)
  {T : ShortComplex Cᵒᵖ} {U : ShortComplex Dᵒᵖ} (φ : T.map F.op ⟶ U)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y 0
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ContravariantModuleFunctor.functor R (F.obj Y) 0

def shortMap : T.map G ⟶ U.map H :=
  IntegralComparison.Ext.SourceExactFunctorModule.shortMap F R Y 0 T ≫ (H).mapShortComplex.map φ

theorem shortMap_id : shortMap F R Y (𝟙 (T.map F.op)) = IntegralComparison.Ext.SourceExactFunctorModule.shortMap F R Y 0 T := by
  exact (congrArg (fun h => IntegralComparison.Ext.SourceExactFunctorModule.shortMap F R Y 0 T ≫ h)
    ((H).mapShortComplex.map_id (T.map F.op))).trans (Category.comp_id _)

variable {A : Cᵒᵖ} {B : Dᵒᵖ} (a : A ⟶ T.X₁) (b : B ⟶ U.X₁)
  (ha : a ≫ T.toCycles = 0) (hb : b ≫ U.toCycles = 0)
  (hT : (ShortComplex.mk a T.toCycles ha).ShortExact)
  (hU : (ShortComplex.mk b U.toCycles hb).ShortExact)
  [Subsingleton (Ext.{z} T.X₁.unop Y 1)] [Subsingleton (Ext.{z} U.X₁.unop (F.obj Y) 1)]
  (g : F.op.obj A ⟶ B) (hg : g ≫ b = F.op.map a ≫ φ.τ₁)

local notation "dT" => OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionHomologyData.data R Y T a ha hT
local notation "dU" => OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionHomologyData.data R (F.obj Y) U b hb hU
local notation "c" => OAI.NumberTheory.PadicHodge.IntegralComparison.ShortCyclesExactFunctor.cycleMap F.op φ
local notation "η" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceExactFunctorModule.component F R Y 0

omit [Subsingleton (Ext.{z} T.X₁.unop Y 1)] [Subsingleton (Ext.{z} U.X₁.unop (F.obj Y) 1)] in
private theorem commi : (η T.cycles ≫ (H).map c) ≫ (H).map U.iCycles =
    (G).map T.iCycles ≫ (η T.X₂ ≫ (H).map φ.τ₂) := by
  calc
    _ = η T.cycles ≫ (H).map (c ≫ U.iCycles) := by rw [Category.assoc, ← (H).map_comp]
    _ = η T.cycles ≫ (H).map (F.op.map T.iCycles ≫ φ.τ₂) := by rw [ShortCyclesExactFunctor.cycleMap_i]
    _ = (η T.cycles ≫ (H).map (F.op.map T.iCycles)) ≫ (H).map φ.τ₂ :=
      (congrArg (fun h => η T.cycles ≫ h) ((H).map_comp (F.op.map T.iCycles) φ.τ₂)).trans
        (Category.assoc _ _ _).symm
    _ = _ := by rw [← IntegralComparison.Ext.SourceExactFunctorModule.naturality, Category.assoc]

omit [Subsingleton (Ext.{z} T.X₁.unop Y 1)] [Subsingleton (Ext.{z} U.X₁.unop (F.obj Y) 1)] in
private theorem commf : (G).map T.toCycles ≫ (η T.cycles ≫ (H).map c) =
    (η T.X₁ ≫ (H).map φ.τ₁) ≫ (H).map U.toCycles := by
  calc
    _ = ((G).map T.toCycles ≫ η T.cycles) ≫ (H).map c := (Category.assoc _ _ _).symm
    _ = (η T.X₁ ≫ (H).map (F.op.map T.toCycles)) ≫ (H).map c := by rw [IntegralComparison.Ext.SourceExactFunctorModule.naturality]
    _ = η T.X₁ ≫ (H).map (F.op.map T.toCycles ≫ c) := by rw [Category.assoc, ← (H).map_comp]
    _ = η T.X₁ ≫ (H).map (φ.τ₁ ≫ U.toCycles) :=
      congrArg (fun h => η T.X₁ ≫ (H).map h) (ShortCyclesExactFunctor.toCycles F.op φ)
    _ = _ := (congrArg (fun h => η T.X₁ ≫ h) ((H).map_comp φ.τ₁ U.toCycles)).trans
      (Category.assoc _ _ _).symm

def data : ShortComplex.LeftHomologyMapData (shortMap F R Y φ) dT dU where
  φK := η T.cycles ≫ (H).map c
  φH := IntegralComparison.Ext.SourceExactFunctorModule.component F R Y 1 A ≫
    (IntegralComparison.Ext.ContravariantModuleFunctor.functor R (F.obj Y) 1).map g
  commi := ExactFunctorHomology.commi F R Y φ
  commf' := by
    have hs : (dT).f' = (G).map T.toCycles := IntegralComparison.Ext.SourceZeroKernels.cycleKernel_lift R Y T
    have ht : (dU).f' = (H).map U.toCycles := IntegralComparison.Ext.SourceZeroKernels.cycleKernel_lift R (F.obj Y) U
    exact (congrArg (fun f => f ≫ (η T.cycles ≫ (H).map c)) hs).trans
      ((commf F R Y φ).trans (congrArg (fun f => (η T.X₁ ≫ (H).map φ.τ₁) ≫ f) ht.symm))
  commπ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    exact (IntegralComparison.Ext.SourceMappedSequenceConnecting.connecting F Y hT hU
      (ShortCyclesExactFunctor.sequenceMap F.op φ a b ha hb g hg) 0 α).symm

include hg in
theorem homology : ShortComplex.homologyMap (shortMap F R Y φ) ≫ (dU).homologyIso.hom =
    (dT).homologyIso.hom ≫ (IntegralComparison.Ext.SourceExactFunctorModule.component F R Y 1 A ≫
      (IntegralComparison.Ext.ContravariantModuleFunctor.functor R (F.obj Y) 1).map g) :=
  (data F R Y φ a b ha hb hT hU g hg).homologyMap_comm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ExactFunctorHomology
