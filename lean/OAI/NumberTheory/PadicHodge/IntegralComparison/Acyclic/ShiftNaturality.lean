import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycleMaps
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ConnectingNaturality

/-! # Shift Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ShiftNaturality

noncomputable section

/-!
# IntegralComparison: dimension shifting in the original Ext groups respects augmented resolution maps
-/

open _root_.CategoryTheory

open Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycleMaps

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (X : C)

private theorem transport {Z W : C} (f : Z ⟶ W) {d d' : ℕ} (hd : d = d')
    {U V : Type z} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (e : U ≃ₗ[R] Ext.{z} X Z d) (e' : V ≃ₗ[R] Ext.{z} X W d)
    (x : U) (y : V) (h : e' y = (Ext.mk₀ f).postcomp X (add_zero d) (e x)) :
    (hd ▸ e') y = (Ext.mk₀ f).postcomp X (add_zero d') ((hd ▸ e) x) := by
  subst d'
  exact h

variable {K L : CochainComplex C ℕ} {Z W : C}
  (ι : (CochainComplex.single₀ C).obj Z ⟶ K) (κ : (CochainComplex.single₀ C).obj W ⟶ L)
  [QuasiIso ι] [QuasiIso κ]
  (hK : ∀ a q, Subsingleton (Ext.{z} X (K.X a) (q + 1)))
  (hL : ∀ a q, Subsingleton (Ext.{z} X (L.X a) (q + 1)))
  (φ : K ⟶ L) (f : Z ⟶ W) (hφ : ι ≫ φ = (CochainComplex.single₀ C).map f ≫ κ)

include hφ

theorem cycles (n q : ℕ) (α : Ext.{z} X (Augmented.ResolutionCycles.differentialSequence K n).cycles (q + 1)) :
    ResolutionShift.cycleExtEquiv R X L κ hL n q
      ((Ext.mk₀ (ShortComplex.cyclesMap (Augmented.ResolutionCycleMaps.differential φ n))).postcomp X (add_zero (q + 1)) α) =
    (Ext.mk₀ f).postcomp X (add_zero (n + q + 2))
      (ResolutionShift.cycleExtEquiv R X K ι hK n q α) := by
  induction n generalizing q with
  | zero =>
    let : Subsingleton (Ext.{z} X (K.X 0) (q + 1)) := hK 0 q
    let : Subsingleton (Ext.{z} X (K.X 0) (q + 1 + 1)) := hK 0 (q + 1)
    let : Subsingleton (Ext.{z} X (L.X 0) (q + 1)) := hL 0 q
    let : Subsingleton (Ext.{z} X (L.X 0) (q + 1 + 1)) := hL 0 (q + 1)
    apply transport R X f (show q + 1 + 1 = 0 + q + 2 by omega)
      (IntegralComparison.Ext.DimensionShift.linearEquivalence X (Augmented.ResolutionCycles.initialSequence_shortExact K ι) (q + 1) R)
      (IntegralComparison.Ext.DimensionShift.linearEquivalence X (Augmented.ResolutionCycles.initialSequence_shortExact L κ) (q + 1) R)
    exact IntegralComparison.Ext.ConnectingNaturality.connecting X
      (Augmented.ResolutionCycles.initialSequence_shortExact K ι) (Augmented.ResolutionCycles.initialSequence_shortExact L κ)
      (Augmented.ResolutionCycleMaps.initial φ ι κ f hφ) (q + 1) α
  | succ n ih =>
    let : Subsingleton (Ext.{z} X (K.X (n + 1)) (q + 1)) := hK (n + 1) q
    let : Subsingleton (Ext.{z} X (K.X (n + 1)) (q + 1 + 1)) := hK (n + 1) (q + 1)
    let : Subsingleton (Ext.{z} X (L.X (n + 1)) (q + 1)) := hL (n + 1) q
    let : Subsingleton (Ext.{z} X (L.X (n + 1)) (q + 1 + 1)) := hL (n + 1) (q + 1)
    apply transport R X f (show n + (q + 1) + 2 = n + 1 + q + 2 by omega)
      ((IntegralComparison.Ext.DimensionShift.linearEquivalence X (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (q + 1) R).trans
        (ResolutionShift.cycleExtEquiv R X K ι hK n (q + 1)))
      ((IntegralComparison.Ext.DimensionShift.linearEquivalence X (Augmented.ResolutionCycles.successiveSequence_shortExact L κ n) (q + 1) R).trans
        (ResolutionShift.cycleExtEquiv R X L κ hL n (q + 1)))
    have h := IntegralComparison.Ext.ConnectingNaturality.connecting X
      (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (Augmented.ResolutionCycles.successiveSequence_shortExact L κ n)
      (Augmented.ResolutionCycleMaps.successive φ n) (q + 1) α
    exact (congrArg (ResolutionShift.cycleExtEquiv R X L κ hL n (q + 1)) h).trans
      (ih (q + 1) (IntegralComparison.Ext.DimensionShift.connecting X (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (q + 1) α))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ShiftNaturality
