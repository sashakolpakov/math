import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ConnectingNaturality

/-! # Homology Data Naturality -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.HomologyDataNaturality.AcyclicHomologyDataNaturality

noncomputable section

/-! # Naturality of the actual connecting-map description of resolution homology -/

open _root_.CategoryTheory

open _root_.CategoryTheory.Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (X : C)
  (T U : ShortComplex C) (φ : T ⟶ U) {A B : C}
  (a : A ⟶ T.X₁) (ha : a ≫ T.toCycles = 0)
  (b : B ⟶ U.X₁) (hb : b ≫ U.toCycles = 0)
  (β : A ⟶ B) (hβ : β ≫ b = a ≫ φ.τ₁)

def sequenceMap : ShortComplex.mk a T.toCycles ha ⟶ ShortComplex.mk b U.toCycles hb where
  τ₁ := β
  τ₂ := φ.τ₁
  τ₃ := ShortComplex.cyclesMap φ
  comm₁₂ := hβ
  comm₂₃ := (ShortComplex.toCycles_naturality φ).symm

variable (hT : (ShortComplex.mk a T.toCycles ha).ShortExact)
  (hU : (ShortComplex.mk b U.toCycles hb).ShortExact)
  [Subsingleton (Ext.{z} X T.X₁ 1)] [Subsingleton (Ext.{z} X U.X₁ 1)]

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 0
local notation "dT" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.data R X T a ha hT
local notation "dU" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.data R X U b hb hU

def data : ShortComplex.LeftHomologyMapData ((F).mapShortComplex.map φ) dT dU where
  φK := (F).map (ShortComplex.cyclesMap φ)
  φH := (NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 1).map β
  commi := by
    change (F).map (ShortComplex.cyclesMap φ) ≫ (F).map U.iCycles =
      (F).map T.iCycles ≫ (F).map φ.τ₂
    rw [← (F).map_comp, ← (F).map_comp, ShortComplex.cyclesMap_i]
  commf' := by
    have ht : (dT).f' = (F).map T.toCycles := NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroKernels.cycleKernel_lift R X T
    have hu : (dU).f' = (F).map U.toCycles := NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroKernels.cycleKernel_lift R X U
    have hc : (F).map T.toCycles ≫ (F).map (ShortComplex.cyclesMap φ) =
        (F).map φ.τ₁ ≫ (F).map U.toCycles := by
      rw [← (F).map_comp, ← (F).map_comp, ShortComplex.toCycles_naturality]
    exact (congrArg (fun g : (F).obj T.X₁ ⟶ (F).obj T.cycles =>
      g ≫ (F).map (ShortComplex.cyclesMap φ)) ht).trans
        (hc.trans (congrArg (fun g : (F).obj U.X₁ ⟶ (F).obj U.cycles => (F).map φ.τ₁ ≫ g) hu).symm)
  commπ := (NumberTheory.PadicHodge.IntegralComparison.Ext.ConnectingNaturality.zero R X hT hU (sequenceMap T U φ a ha b hb β hβ)).symm

include hβ in
theorem homologyIso_naturality :
    ShortComplex.homologyMap ((F).mapShortComplex.map φ) ≫
      (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.homologyIso R X U b hb hU).hom =
        (NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData.homologyIso R X T a ha hT).hom ≫
          (NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 1).map β :=
  (data R X T U φ a ha b hb β hβ hT hU).homologyMap_comm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Acyclic.HomologyDataNaturality.AcyclicHomologyDataNaturality
