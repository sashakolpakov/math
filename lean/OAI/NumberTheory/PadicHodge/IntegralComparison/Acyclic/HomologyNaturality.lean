import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ConnectingNaturality

/-! # Homology Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.HomologyNaturality

noncomputable section

/-!
# IntegralComparison: the original acyclic-resolution homology calculation respects maps of short complexes
-/

open _root_.CategoryTheory

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (X : C)
  {T U : ShortComplex C} {A B : C} (a : A ⟶ T.X₁) (b : B ⟶ U.X₁)
  (ha : a ≫ T.toCycles = 0) (hb : b ≫ U.toCycles = 0)
  (hT : (ShortComplex.mk a T.toCycles ha).ShortExact)
  (hU : (ShortComplex.mk b U.toCycles hb).ShortExact)
  [Subsingleton (Ext.{z} X T.X₁ 1)] [Subsingleton (Ext.{z} X U.X₁ 1)]
  (φ : T ⟶ U) (g : A ⟶ B) (hg : g ≫ b = a ≫ φ.τ₁)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 0
local notation "dT" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.data R X T a ha hT
local notation "dU" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.data R X U b hb hU

def sequenceMap : ShortComplex.mk a T.toCycles ha ⟶ ShortComplex.mk b U.toCycles hb where
  τ₁ := g
  τ₂ := φ.τ₁
  τ₃ := ShortComplex.cyclesMap φ
  comm₁₂ := hg
  comm₂₃ := (ShortComplex.toCycles_naturality φ).symm

private theorem source_f' : (dT).f' = (F).map T.toCycles := IntegralComparison.Ext.ZeroKernels.cycleKernel_lift R X T

private theorem target_f' : (dU).f' = (F).map U.toCycles := IntegralComparison.Ext.ZeroKernels.cycleKernel_lift R X U

def data : ShortComplex.LeftHomologyMapData (((F).mapShortComplex).map φ) dT dU where
  φK := (F).map (ShortComplex.cyclesMap φ)
  φH := (IntegralComparison.Ext.ModuleFunctor.functor R X 1).map g
  commi := by
    change (F).map (ShortComplex.cyclesMap φ) ≫ (F).map U.iCycles = (F).map T.iCycles ≫ (F).map φ.τ₂
    rw [← (F).map_comp, ShortComplex.cyclesMap_i, (F).map_comp]
  commf' := by
    have hm : (F).map T.toCycles ≫ (F).map (ShortComplex.cyclesMap φ) =
        (F).map φ.τ₁ ≫ (F).map U.toCycles := by
      rw [← (F).map_comp, ShortComplex.toCycles_naturality, (F).map_comp]
    exact (congrArg (fun a => a ≫ (F).map (ShortComplex.cyclesMap φ)) (source_f' R X a ha hT)).trans
      (hm.trans (congrArg (fun a => (F).map φ.τ₁ ≫ a) (target_f' R X b hb hU).symm))
  commπ := (IntegralComparison.Ext.ConnectingNaturality.zero R X hT hU (sequenceMap a b ha hb φ g hg)).symm

include hg in
theorem homology : ShortComplex.homologyMap (((F).mapShortComplex).map φ) ≫ (dU).homologyIso.hom =
    (dT).homologyIso.hom ≫ (IntegralComparison.Ext.ModuleFunctor.functor R X 1).map g :=
  (data R X a b ha hb hT hU φ g hg).homologyMap_comm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.HomologyNaturality
