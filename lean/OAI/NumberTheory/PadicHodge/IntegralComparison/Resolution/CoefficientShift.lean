import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.CoefficientNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionShift

/-! # Coefficient Shift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CoefficientShift

noncomputable section

/-! Iterated source dimension shifting in original Ext is natural in
the coefficient object. -/

open _root_.CategoryTheory

open Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] {Y Y' : C} (g : Y ⟶ Y')

private theorem transport {Z : C} {d d' : ℕ} (hd : d = d')
    {U V : Type z} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (e : U ≃ₗ[R] Ext.{z} Z Y d) (e' : V ≃ₗ[R] Ext.{z} Z Y' d)
    (x : U) (y : V)
    (h : e' y = (Ext.mk₀ g).postcomp Z (Nat.add_zero d) (e x)) :
    (hd ▸ e') y = (Ext.mk₀ g).postcomp Z (Nat.add_zero d') ((hd ▸ e) x) := by
  subst d'
  exact h

variable (K : CochainComplex Cᵒᵖ ℕ) {Z : Cᵒᵖ}
  (ι : (CochainComplex.single₀ Cᵒᵖ).obj Z ⟶ K) [QuasiIso ι]
  (hK : ∀ a q, Subsingleton (Ext.{z} (K.X a).unop Y (q + 1)))
  (hK' : ∀ a q, Subsingleton (Ext.{z} (K.X a).unop Y' (q + 1)))

theorem cycles (n q : ℕ)
    (α : Ext.{z} (Augmented.ResolutionCycles.differentialSequence K n).cycles.unop Y (q + 1)) :
    Contravariant.ResolutionShift.cycleExtEquiv R Y' K ι hK' n q
      ((Ext.mk₀ g).postcomp (Augmented.ResolutionCycles.differentialSequence K n).cycles.unop (Nat.add_zero (q + 1)) α) =
      (Ext.mk₀ g).postcomp Z.unop (Nat.add_zero (n + q + 2))
        (Contravariant.ResolutionShift.cycleExtEquiv R Y K ι hK n q α) := by
  induction n generalizing q with
  | zero =>
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.initialSequence K ι).unop.X₂ Y (q + 1)) := hK 0 q
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.initialSequence K ι).unop.X₂ Y (q + 1 + 1)) := hK 0 (q + 1)
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.initialSequence K ι).unop.X₂ Y' (q + 1)) := hK' 0 q
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.initialSequence K ι).unop.X₂ Y' (q + 1 + 1)) := hK' 0 (q + 1)
    apply transport R g (show q + 1 + 1 = 0 + q + 2 by omega)
      (IntegralComparison.Ext.SourceDimensionShift.linearEquivalence (Augmented.ResolutionCycles.initialSequence_shortExact K ι).unop Y (q + 1) R)
      (IntegralComparison.Ext.SourceDimensionShift.linearEquivalence (Augmented.ResolutionCycles.initialSequence_shortExact K ι).unop Y' (q + 1) R)
    exact IntegralComparison.Ext.CoefficientNaturality.connecting g (Augmented.ResolutionCycles.initialSequence_shortExact K ι).unop (q + 1) α
  | succ n ih =>
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.successiveSequence K n).unop.X₂ Y (q + 1)) := hK (n + 1) q
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.successiveSequence K n).unop.X₂ Y (q + 1 + 1)) := hK (n + 1) (q + 1)
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.successiveSequence K n).unop.X₂ Y' (q + 1)) := hK' (n + 1) q
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.successiveSequence K n).unop.X₂ Y' (q + 1 + 1)) := hK' (n + 1) (q + 1)
    apply transport R g (show n + (q + 1) + 2 = n + 1 + q + 2 by omega)
      ((IntegralComparison.Ext.SourceDimensionShift.linearEquivalence
        (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n).unop Y (q + 1) R).trans
        (Contravariant.ResolutionShift.cycleExtEquiv R Y K ι hK n (q + 1)))
      ((IntegralComparison.Ext.SourceDimensionShift.linearEquivalence
        (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n).unop Y' (q + 1) R).trans
        (Contravariant.ResolutionShift.cycleExtEquiv R Y' K ι hK' n (q + 1)))
    have h := IntegralComparison.Ext.CoefficientNaturality.connecting g
      (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n).unop (q + 1) α
    exact (congrArg (Contravariant.ResolutionShift.cycleExtEquiv R Y' K ι hK' n (q + 1)) h).trans
      (ih (q + 1) (IntegralComparison.Ext.SourceDimensionShift.connecting
        (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n).unop Y (q + 1) α))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Resolution.CoefficientShift
