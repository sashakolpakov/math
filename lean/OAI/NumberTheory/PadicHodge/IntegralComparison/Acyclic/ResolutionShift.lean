import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.DimensionShift

/-! # Resolution Shift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift

noncomputable section

/-!
# IntegralComparison: coefficient-linear dimension shifting along an actual acyclic resolution
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v z

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type*) [CommRing R] [Linear R C] (X : C)
  (K : CochainComplex C ℕ) {Z : C} (ι : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ι]
  (hK : ∀ a q, Subsingleton (Ext.{z} X (K.X a) (q + 1)))

def cycleExtEquiv (n q : ℕ) :
    Ext.{z} X (Augmented.ResolutionCycles.differentialSequence K n).cycles (q + 1) ≃ₗ[R] Ext.{z} X Z (n + q + 2) := by
  induction n generalizing q with
  | zero =>
    let : Subsingleton (Ext.{z} X (K.X 0) (q + 1)) := hK 0 q
    let : Subsingleton (Ext.{z} X (K.X 0) (q + 1 + 1)) := hK 0 (q + 1)
    have h : q + 1 + 1 = 0 + q + 2 := by omega
    exact h ▸ IntegralComparison.Ext.DimensionShift.linearEquivalence X (Augmented.ResolutionCycles.initialSequence_shortExact K ι) (q + 1) R
  | succ n ih =>
    let : Subsingleton (Ext.{z} X (K.X (n + 1)) (q + 1)) := hK (n + 1) q
    let : Subsingleton (Ext.{z} X (K.X (n + 1)) (q + 1 + 1)) := hK (n + 1) (q + 1)
    have h : n + (q + 1) + 2 = n + 1 + q + 2 := by omega
    exact h ▸ (IntegralComparison.Ext.DimensionShift.linearEquivalence X (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (q + 1) R).trans
      (ih (q + 1))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift
