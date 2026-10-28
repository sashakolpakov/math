import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceModule
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift

/-! # Source Shift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.SourceShift

noncomputable section

/-! Native dimension shifting commutes with precomposition in the source of Ext. -/

open _root_.CategoryTheory

open Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] {X X' : C} (f : X' ⟶ X)

private theorem transport {Z : C} {d d' : ℕ} (hd : d = d')
    {U V : Type z} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (e : U ≃ₗ[R] Ext.{z} X Z d) (e' : V ≃ₗ[R] Ext.{z} X' Z d)
    (x : U) (y : V) (h : e' y = IntegralComparison.Ext.SourceModule.component R f d Z (e x)) :
    (hd ▸ e') y = IntegralComparison.Ext.SourceModule.component R f d' Z ((hd ▸ e) x) := by
  subst d'
  exact h

variable (K : CochainComplex C ℕ) {Z : C} (ι : (CochainComplex.single₀ C).obj Z ⟶ K)
  [QuasiIso ι]
  (hK : ∀ a q, Subsingleton (Ext.{z} X (K.X a) (q + 1)))
  (hK' : ∀ a q, Subsingleton (Ext.{z} X' (K.X a) (q + 1)))

theorem cycles (n q : ℕ) (α : Ext.{z} X (Augmented.ResolutionCycles.differentialSequence K n).cycles (q + 1)) :
    ResolutionShift.cycleExtEquiv R X' K ι hK' n q
      (IntegralComparison.Ext.SourceModule.component R f (q + 1) (Augmented.ResolutionCycles.differentialSequence K n).cycles α) =
    IntegralComparison.Ext.SourceModule.component R f (n + q + 2) Z
      (ResolutionShift.cycleExtEquiv R X K ι hK n q α) := by
  induction n generalizing q with
  | zero =>
    let : Subsingleton (Ext.{z} X (K.X 0) (q + 1)) := hK 0 q
    let : Subsingleton (Ext.{z} X (K.X 0) (q + 1 + 1)) := hK 0 (q + 1)
    let : Subsingleton (Ext.{z} X' (K.X 0) (q + 1)) := hK' 0 q
    let : Subsingleton (Ext.{z} X' (K.X 0) (q + 1 + 1)) := hK' 0 (q + 1)
    apply transport R f (show q + 1 + 1 = 0 + q + 2 by omega)
      (IntegralComparison.Ext.DimensionShift.linearEquivalence X (Augmented.ResolutionCycles.initialSequence_shortExact K ι) (q + 1) R)
      (IntegralComparison.Ext.DimensionShift.linearEquivalence X' (Augmented.ResolutionCycles.initialSequence_shortExact K ι) (q + 1) R)
    exact IntegralComparison.Ext.SourceModule.connecting R f (Augmented.ResolutionCycles.initialSequence_shortExact K ι) (q + 1) α
  | succ n ih =>
    let : Subsingleton (Ext.{z} X (K.X (n + 1)) (q + 1)) := hK (n + 1) q
    let : Subsingleton (Ext.{z} X (K.X (n + 1)) (q + 1 + 1)) := hK (n + 1) (q + 1)
    let : Subsingleton (Ext.{z} X' (K.X (n + 1)) (q + 1)) := hK' (n + 1) q
    let : Subsingleton (Ext.{z} X' (K.X (n + 1)) (q + 1 + 1)) := hK' (n + 1) (q + 1)
    apply transport R f (show n + (q + 1) + 2 = n + 1 + q + 2 by omega)
      ((IntegralComparison.Ext.DimensionShift.linearEquivalence X (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (q + 1) R).trans
        (ResolutionShift.cycleExtEquiv R X K ι hK n (q + 1)))
      ((IntegralComparison.Ext.DimensionShift.linearEquivalence X' (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (q + 1) R).trans
        (ResolutionShift.cycleExtEquiv R X' K ι hK' n (q + 1)))
    have h := IntegralComparison.Ext.SourceModule.connecting R f (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (q + 1) α
    exact (congrArg (ResolutionShift.cycleExtEquiv R X' K ι hK' n (q + 1)) h).trans
      (ih (q + 1) (IntegralComparison.Ext.DimensionShift.connecting X (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (q + 1) α))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.SourceShift
