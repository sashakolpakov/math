import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionShift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.CyclesExactFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.MappedSequenceConnecting

/-! # Exact Functor Shift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ExactFunctorShift

noncomputable section

/-! The actual dimension-shift comparison commutes with exact functors and native cycle transport. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] (X : C)

private theorem transport {Z : C} {d d' : ℕ} (hd : d = d')
    {U V : Type z} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (e : U ≃ₗ[R] Ext.{z} X Z d) (e' : V ≃ₗ[R] Ext.{z} (F.obj X) (F.obj Z) d)
    (x : U) (y : V) (h : e' y = (e x).mapExactFunctor F) :
    (hd ▸ e') y = ((hd ▸ e) x).mapExactFunctor F := by
  subst d'
  exact h

variable (K : CochainComplex C ℕ)

local notation "L" => Functor.obj (Functor.mapHomologicalComplex F (ComplexShape.up ℕ)) K

def cycleMap (n q : ℕ) (α : Ext.{z} X (Augmented.ResolutionCycles.differentialSequence K n).cycles (q + 1)) :
    Ext.{z} (F.obj X) (Augmented.ResolutionCycles.differentialSequence L n).cycles (q + 1) :=
  (Ext.mk₀ (Augmented.CyclesExactFunctor.cyclesIso F K n).hom).postcomp
    (F.obj X) (add_zero (q + 1)) (α.mapExactFunctor F)

variable {Z : C} (ι : (CochainComplex.single₀ C).obj Z ⟶ K)
  (κ : (CochainComplex.single₀ D).obj (F.obj Z) ⟶
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) (hκ : κ.f 0 = F.map (ι.f 0))
  [QuasiIso ι] [QuasiIso κ]
  (hK : ∀ a q, Subsingleton (Ext.{z} X (K.X a) (q + 1)))
  (hL : ∀ a q, Subsingleton (Ext.{z} (F.obj X)
    (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).X a) (q + 1)))

include hκ in
theorem cycles (n q : ℕ) (α : Ext.{z} X (Augmented.ResolutionCycles.differentialSequence K n).cycles (q + 1)) :
    ResolutionShift.cycleExtEquiv R (F.obj X) L κ hL n q (cycleMap F X K n q α) =
      (ResolutionShift.cycleExtEquiv R X K ι hK n q α).mapExactFunctor F := by
  induction n generalizing q with
  | zero =>
    let : Subsingleton (Ext.{z} X (K.X 0) (q + 1)) := hK 0 q
    let : Subsingleton (Ext.{z} X (K.X 0) (q + 1 + 1)) := hK 0 (q + 1)
    let : Subsingleton (Ext.{z} (F.obj X) ((L).X 0) (q + 1)) := hL 0 q
    let : Subsingleton (Ext.{z} (F.obj X) ((L).X 0) (q + 1 + 1)) := hL 0 (q + 1)
    apply transport F R X (show q + 1 + 1 = 0 + q + 2 by omega)
      (IntegralComparison.Ext.DimensionShift.linearEquivalence X (Augmented.ResolutionCycles.initialSequence_shortExact K ι) (q + 1) R)
      (IntegralComparison.Ext.DimensionShift.linearEquivalence (F.obj X) (Augmented.ResolutionCycles.initialSequence_shortExact L κ) (q + 1) R)
    have h := IntegralComparison.Ext.MappedSequenceConnecting.connecting F X (Augmented.ResolutionCycles.initialSequence_shortExact K ι)
      (Augmented.ResolutionCycles.initialSequence_shortExact L κ) (Augmented.CyclesExactFunctor.initialIso F K ι κ hκ).hom (q + 1) α
    exact h.trans (Ext.comp_mk₀_id _)
  | succ n ih =>
    let : Subsingleton (Ext.{z} X (K.X (n + 1)) (q + 1)) := hK (n + 1) q
    let : Subsingleton (Ext.{z} X (K.X (n + 1)) (q + 1 + 1)) := hK (n + 1) (q + 1)
    let : Subsingleton (Ext.{z} (F.obj X) ((L).X (n + 1)) (q + 1)) := hL (n + 1) q
    let : Subsingleton (Ext.{z} (F.obj X) ((L).X (n + 1)) (q + 1 + 1)) := hL (n + 1) (q + 1)
    apply transport F R X (show n + (q + 1) + 2 = n + 1 + q + 2 by omega)
      ((IntegralComparison.Ext.DimensionShift.linearEquivalence X (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (q + 1) R).trans
        (ResolutionShift.cycleExtEquiv R X K ι hK n (q + 1)))
      ((IntegralComparison.Ext.DimensionShift.linearEquivalence (F.obj X) (Augmented.ResolutionCycles.successiveSequence_shortExact L κ n) (q + 1) R).trans
        (ResolutionShift.cycleExtEquiv R (F.obj X) L κ hL n (q + 1)))
    have h := IntegralComparison.Ext.MappedSequenceConnecting.connecting F X (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n)
      (Augmented.ResolutionCycles.successiveSequence_shortExact L κ n) (Augmented.CyclesExactFunctor.successiveIso F K n).hom (q + 1) α
    exact (congrArg (ResolutionShift.cycleExtEquiv R (F.obj X) L κ hL n (q + 1)) h).trans
      (ih (q + 1) (IntegralComparison.Ext.DimensionShift.connecting X (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (q + 1) α))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ExactFunctorShift
