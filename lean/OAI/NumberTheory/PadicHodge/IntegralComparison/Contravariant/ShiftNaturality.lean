import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionShift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycleMaps
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceConnectingNaturality

/-! # Shift Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ShiftNaturality

noncomputable section

/-!
# IntegralComparison: source dimension shifting in the original Ext groups respects augmented resolution maps
-/

open _root_.CategoryTheory

open Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycleMaps

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (Y : C)

private theorem transport {Z W : Cᵒᵖ} (f : Z ⟶ W) {d d' : ℕ} (hd : d = d')
    {U V : Type z} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (e : U ≃ₗ[R] Ext.{z} Z.unop Y d) (e' : V ≃ₗ[R] Ext.{z} W.unop Y d)
    (x : U) (y : V) (h : e' y = (Ext.mk₀ f.unop).precomp Y (zero_add d) (e x)) :
    (hd ▸ e') y = (Ext.mk₀ f.unop).precomp Y (zero_add d') ((hd ▸ e) x) := by
  subst d'
  exact h

variable {K L : CochainComplex Cᵒᵖ ℕ} {Z W : Cᵒᵖ}
  (ι : (CochainComplex.single₀ Cᵒᵖ).obj Z ⟶ K) (κ : (CochainComplex.single₀ Cᵒᵖ).obj W ⟶ L)
  [QuasiIso ι] [QuasiIso κ]
  (hK : ∀ a q, Subsingleton (Ext.{z} (K.X a).unop Y (q + 1)))
  (hL : ∀ a q, Subsingleton (Ext.{z} (L.X a).unop Y (q + 1)))
  (φ : K ⟶ L) (f : Z ⟶ W) (hφ : ι ≫ φ = (CochainComplex.single₀ Cᵒᵖ).map f ≫ κ)

include hφ

theorem cycles (n q : ℕ) (α : Ext.{z} (Augmented.ResolutionCycles.differentialSequence K n).cycles.unop Y (q + 1)) :
    ResolutionShift.cycleExtEquiv R Y L κ hL n q
      ((Ext.mk₀ (ShortComplex.cyclesMap (Augmented.ResolutionCycleMaps.differential φ n)).unop).precomp Y (zero_add (q + 1)) α) =
    (Ext.mk₀ f.unop).precomp Y (zero_add (n + q + 2))
      (ResolutionShift.cycleExtEquiv R Y K ι hK n q α) := by
  induction n generalizing q with
  | zero =>
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.initialSequence K ι).unop.X₂ Y (q + 1)) := hK 0 q
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.initialSequence K ι).unop.X₂ Y (q + 1 + 1)) := hK 0 (q + 1)
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.initialSequence L κ).unop.X₂ Y (q + 1)) := hL 0 q
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.initialSequence L κ).unop.X₂ Y (q + 1 + 1)) := hL 0 (q + 1)
    apply transport R Y f (show q + 1 + 1 = 0 + q + 2 by omega)
      (IntegralComparison.Ext.SourceDimensionShift.linearEquivalence (Augmented.ResolutionCycles.initialSequence_shortExact K ι).unop Y (q + 1) R)
      (IntegralComparison.Ext.SourceDimensionShift.linearEquivalence (Augmented.ResolutionCycles.initialSequence_shortExact L κ).unop Y (q + 1) R)
    exact IntegralComparison.Ext.SourceConnectingNaturality.connecting Y
      (Augmented.ResolutionCycles.initialSequence_shortExact K ι) (Augmented.ResolutionCycles.initialSequence_shortExact L κ)
      (Augmented.ResolutionCycleMaps.initial φ ι κ f hφ) (q + 1) α
  | succ n ih =>
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.successiveSequence K n).unop.X₂ Y (q + 1)) := hK (n + 1) q
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.successiveSequence K n).unop.X₂ Y (q + 1 + 1)) := hK (n + 1) (q + 1)
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.successiveSequence L n).unop.X₂ Y (q + 1)) := hL (n + 1) q
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.successiveSequence L n).unop.X₂ Y (q + 1 + 1)) := hL (n + 1) (q + 1)
    apply transport R Y f (show n + (q + 1) + 2 = n + 1 + q + 2 by omega)
      ((IntegralComparison.Ext.SourceDimensionShift.linearEquivalence (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n).unop Y (q + 1) R).trans
        (ResolutionShift.cycleExtEquiv R Y K ι hK n (q + 1)))
      ((IntegralComparison.Ext.SourceDimensionShift.linearEquivalence (Augmented.ResolutionCycles.successiveSequence_shortExact L κ n).unop Y (q + 1) R).trans
        (ResolutionShift.cycleExtEquiv R Y L κ hL n (q + 1)))
    have h := IntegralComparison.Ext.SourceConnectingNaturality.connecting Y
      (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (Augmented.ResolutionCycles.successiveSequence_shortExact L κ n)
      (Augmented.ResolutionCycleMaps.successive φ n) (q + 1) α
    exact (congrArg (ResolutionShift.cycleExtEquiv R Y L κ hL n (q + 1)) h).trans
      (ih (q + 1) (IntegralComparison.Ext.SourceDimensionShift.connecting (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n).unop Y (q + 1) α))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ShiftNaturality
