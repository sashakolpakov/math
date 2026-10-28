import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionHomologyData

/-! # Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison

noncomputable section

/-!
# IntegralComparison: sections of an actual acyclic resolution compute positive Ext
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (X : C)
  (K : CochainComplex C ℕ) {Z : C} (ι : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ι]
  (hK : ∀ a q, Subsingleton (Ext.{z} X (K.X a) (q + 1)))

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 0

def complex : CochainComplex (ModuleCat.{z} R) ℕ :=
  ((F).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

def shortHomologyIso (n : ℕ) : ((Augmented.ResolutionCycles.differentialSequence K n).map F).homology ≅
    ModuleCat.of R (Ext.{z} X Z (n + 1)) := by
  cases n with
  | zero =>
    let : Subsingleton (Ext.{z} X (K.X 0) 1) := hK 0 0
    exact ResolutionHomologyData.homologyIso R X (Augmented.ResolutionCycles.differentialSequence K 0)
      (Augmented.ResolutionCycles.augmentation K ι) (Augmented.ResolutionCycles.initialSequence K ι).zero (Augmented.ResolutionCycles.initialSequence_shortExact K ι)
  | succ n =>
    let : Subsingleton (Ext.{z} X (K.X (n + 1)) 1) := hK (n + 1) 0
    have h : n + 0 + 2 = n + 1 + 1 := by omega
    exact ResolutionHomologyData.homologyIso R X (Augmented.ResolutionCycles.differentialSequence K (n + 1))
      (Augmented.ResolutionCycles.successiveSequence K n).f (Augmented.ResolutionCycles.successiveSequence K n).zero (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) ≪≫
      (h ▸ (ResolutionShift.cycleExtEquiv R X K ι hK n 0).toModuleIso)

def positiveHomologyIso (n : ℕ) : (complex R X K).homology (n + 1) ≅
    ModuleCat.of R (Ext.{z} X Z (n + 1)) :=
  (complex R X K).homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp) ≪≫
    shortHomologyIso R X K ι hK n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison
