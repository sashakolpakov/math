import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionShift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionHomologyData

/-! # Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.Resolution.Comparison

noncomputable section

/-!
# IntegralComparison: an acyclic source resolution computes positive original Ext
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

open Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (Y : C)
  (K : CochainComplex Cᵒᵖ ℕ) {Z : Cᵒᵖ} (ι : (CochainComplex.single₀ Cᵒᵖ).obj Z ⟶ K) [QuasiIso ι]
  (hK : ∀ a q, Subsingleton (Ext.{z} (K.X a).unop Y (q + 1)))

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y 0

def complex : CochainComplex (ModuleCat.{z} R) ℕ :=
  ((F).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

def shortHomologyIso (n : ℕ) : ((Augmented.ResolutionCycles.differentialSequence K n).map F).homology ≅
    ModuleCat.of R (Ext.{z} Z.unop Y (n + 1)) := by
  cases n with
  | zero =>
    let : Subsingleton (Ext.{z} (K.X 0).unop Y 1) := hK 0 0
    exact ResolutionHomologyData.homologyIso R Y (Augmented.ResolutionCycles.differentialSequence K 0)
      (Augmented.ResolutionCycles.augmentation K ι) (Augmented.ResolutionCycles.initialSequence K ι).zero (Augmented.ResolutionCycles.initialSequence_shortExact K ι)
  | succ n =>
    let : Subsingleton (Ext.{z} (K.X (n + 1)).unop Y 1) := hK (n + 1) 0
    have h : n + 0 + 2 = n + 1 + 1 := by omega
    exact ResolutionHomologyData.homologyIso R Y (Augmented.ResolutionCycles.differentialSequence K (n + 1))
      (Augmented.ResolutionCycles.successiveSequence K n).f (Augmented.ResolutionCycles.successiveSequence K n).zero (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) ≪≫
      (h ▸ (ResolutionShift.cycleExtEquiv R Y K ι hK n 0).toModuleIso)

def positiveHomologyIso (n : ℕ) : (complex R Y K).homology (n + 1) ≅
    ModuleCat.of R (Ext.{z} Z.unop Y (n + 1)) :=
  (complex R Y K).homologyIsoSc' n (n + 1) (n + 2) (by simp) (by simp) ≪≫
    shortHomologyIso R Y K ι hK n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.Resolution.Comparison
