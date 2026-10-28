import OAI.NumberTheory.PadicHodge.IntegralComparison.Mapped.AugmentedCycleMaps
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionShift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceMappedSequenceConnecting

/-! # Mixed Resolution Dimension Shift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.MixedResolutionDimensionShift

noncomputable section

/-! Dimension shifting is natural for a map from an exactly transported
resolution to a second acyclic resolution. Only the endpoint terms need be
acyclic for their respective coefficients. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

attribute [local instance] preservesFiniteLimits_op preservesFiniteColimits_op

open Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] (Y : C)

private theorem transport {Z : Cᵒᵖ} {W : Dᵒᵖ} (g : F.op.obj Z ⟶ W)
    {d d' : ℕ} (hd : d = d')
    {U V : Type z} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (e : U ≃ₗ[R] Ext.{z} Z.unop Y d) (e' : V ≃ₗ[R] Ext.{z} W.unop (F.obj Y) d)
    (x : U) (y : V)
    (h : e' y = (Ext.mk₀ g.unop).precomp (F.obj Y) (zero_add d) ((e x).mapExactFunctor F)) :
    (hd ▸ e') y = (Ext.mk₀ g.unop).precomp (F.obj Y) (zero_add d') (((hd ▸ e) x).mapExactFunctor F) := by
  subst d'
  exact h

variable {K : CochainComplex Cᵒᵖ ℕ} {L : CochainComplex Dᵒᵖ ℕ}
  (φ : (F.op.mapHomologicalComplex (.up ℕ)).obj K ⟶ L)

def cycleMap (n q : ℕ) (α : Ext.{z} (Augmented.ResolutionCycles.differentialSequence K n).cycles.unop Y (q + 1)) :
    Ext.{z} (Augmented.ResolutionCycles.differentialSequence L n).cycles.unop (F.obj Y) (q + 1) :=
  (Ext.mk₀ (Mapped.AugmentedCycleMaps.cycles F.op φ n).unop).precomp
    (F.obj Y) (zero_add (q + 1)) (α.mapExactFunctor F)

variable {Z : Cᵒᵖ} {W : Dᵒᵖ} (ι : (CochainComplex.single₀ Cᵒᵖ).obj Z ⟶ K)
  (κ : (CochainComplex.single₀ Dᵒᵖ).obj W ⟶ L) (g : F.op.obj Z ⟶ W)
  (h : g ≫ κ.f 0 = F.op.map (ι.f 0) ≫ φ.f 0)
  [QuasiIso ι] [QuasiIso κ]
  (hK : ∀ a q, Subsingleton (Ext.{z} (K.X a).unop Y (q + 1)))
  (hL : ∀ a q, Subsingleton (Ext.{z} (L.X a).unop (F.obj Y) (q + 1)))

include h in
theorem cycles (n q : ℕ) (α : Ext.{z} (Augmented.ResolutionCycles.differentialSequence K n).cycles.unop Y (q + 1)) :
    Contravariant.ResolutionShift.cycleExtEquiv R (F.obj Y) L κ hL n q (cycleMap F Y φ n q α) =
      (Ext.mk₀ g.unop).precomp (F.obj Y) (zero_add (n + q + 2))
        ((Contravariant.ResolutionShift.cycleExtEquiv R Y K ι hK n q α).mapExactFunctor F) := by
  induction n generalizing q with
  | zero =>
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.initialSequence K ι).unop.X₂ Y (q + 1)) := hK 0 q
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.initialSequence K ι).unop.X₂ Y (q + 1 + 1)) := hK 0 (q + 1)
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.initialSequence L κ).unop.X₂ (F.obj Y) (q + 1)) := hL 0 q
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.initialSequence L κ).unop.X₂ (F.obj Y) (q + 1 + 1)) := hL 0 (q + 1)
    apply transport F R Y g (show q + 1 + 1 = 0 + q + 2 by omega)
      (IntegralComparison.Ext.SourceDimensionShift.linearEquivalence (Augmented.ResolutionCycles.initialSequence_shortExact K ι).unop Y (q + 1) R)
      (IntegralComparison.Ext.SourceDimensionShift.linearEquivalence (Augmented.ResolutionCycles.initialSequence_shortExact L κ).unop (F.obj Y) (q + 1) R)
    exact IntegralComparison.Ext.SourceMappedSequenceConnecting.connecting F Y (Augmented.ResolutionCycles.initialSequence_shortExact K ι)
      (Augmented.ResolutionCycles.initialSequence_shortExact L κ) (Mapped.AugmentedCycleMaps.initial F.op φ ι κ g h) (q + 1) α
  | succ n ih =>
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.successiveSequence K n).unop.X₂ Y (q + 1)) := hK (n + 1) q
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.successiveSequence K n).unop.X₂ Y (q + 1 + 1)) := hK (n + 1) (q + 1)
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.successiveSequence L n).unop.X₂ (F.obj Y) (q + 1)) := hL (n + 1) q
    let : Subsingleton (Ext.{z} (Augmented.ResolutionCycles.successiveSequence L n).unop.X₂ (F.obj Y) (q + 1 + 1)) := hL (n + 1) (q + 1)
    apply transport F R Y g (show n + (q + 1) + 2 = n + 1 + q + 2 by omega)
      ((IntegralComparison.Ext.SourceDimensionShift.linearEquivalence (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n).unop Y (q + 1) R).trans
        (Contravariant.ResolutionShift.cycleExtEquiv R Y K ι hK n (q + 1)))
      ((IntegralComparison.Ext.SourceDimensionShift.linearEquivalence (Augmented.ResolutionCycles.successiveSequence_shortExact L κ n).unop (F.obj Y) (q + 1) R).trans
        (Contravariant.ResolutionShift.cycleExtEquiv R (F.obj Y) L κ hL n (q + 1)))
    have hc := IntegralComparison.Ext.SourceMappedSequenceConnecting.connecting F Y (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n)
      (Augmented.ResolutionCycles.successiveSequence_shortExact L κ n) (Mapped.AugmentedCycleMaps.successive F.op φ n) (q + 1) α
    exact (congrArg (Contravariant.ResolutionShift.cycleExtEquiv R (F.obj Y) L κ hL n (q + 1)) hc).trans
      (ih (q + 1) (IntegralComparison.Ext.SourceDimensionShift.connecting (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n).unop Y (q + 1) α))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.MixedResolutionDimensionShift
