import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceDimensionShift

/-! # Resolution Shift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionShift

noncomputable section

/-! Coefficient-linear source dimension shifting along an actual augmented resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

open Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v z

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type*) [CommRing R] [Linear R C] (Y : C)
  (K : CochainComplex Cᵒᵖ ℕ) {Z : Cᵒᵖ} (ι : (CochainComplex.single₀ Cᵒᵖ).obj Z ⟶ K) [QuasiIso ι]
  (hK : ∀ a q, Subsingleton (Ext.{z} (K.X a).unop Y (q + 1)))

def cycleExtEquiv (n q : ℕ) :
    Ext.{z} (Augmented.ResolutionCycles.differentialSequence K n).cycles.unop Y (q + 1) ≃ₗ[R] Ext.{z} Z.unop Y (n + q + 2) := by
  induction n generalizing q with
  | zero =>
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.initialSequence K ι).unop.X₂ Y (q + 1)) := hK 0 q
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.initialSequence K ι).unop.X₂ Y (q + 1 + 1)) := hK 0 (q + 1)
    have h : q + 1 + 1 = 0 + q + 2 := by omega
    exact h ▸ IntegralComparison.Ext.SourceDimensionShift.linearEquivalence (Augmented.ResolutionCycles.initialSequence_shortExact K ι).unop Y (q + 1) R
  | succ n ih =>
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.successiveSequence K n).unop.X₂ Y (q + 1)) := hK (n + 1) q
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.successiveSequence K n).unop.X₂ Y (q + 1 + 1)) := hK (n + 1) (q + 1)
    have h : n + (q + 1) + 2 = n + 1 + q + 2 := by omega
    exact h ▸ (IntegralComparison.Ext.SourceDimensionShift.linearEquivalence
      (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n).unop Y (q + 1) R).trans (ih (q + 1))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionShift
