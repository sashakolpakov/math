import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.HomologyNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ShiftNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.Resolution

/-! # Short Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ShortNaturality.Comparison

noncomputable section

/-!
# IntegralComparison: naturality of the positive-degree acyclic source-resolution comparison on short complexes
-/

open _root_.CategoryTheory

open Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycleMaps

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (Y : C)

private theorem transport {Z W : Cᵒᵖ} (f : Z ⟶ W) {d d' : ℕ} (hd : d = d')
    {U V : Type z} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (e : U ≃ₗ[R] Ext.{z} Z.unop Y d) (e' : V ≃ₗ[R] Ext.{z} W.unop Y d)
    (a : ModuleCat.of R U ⟶ ModuleCat.of R V)
    (h : a ≫ e'.toModuleIso.hom = e.toModuleIso.hom ≫ (IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y d).map f) :
    a ≫ (hd ▸ e').toModuleIso.hom = (hd ▸ e).toModuleIso.hom ≫ (IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y d').map f := by
  subst d'
  exact h

variable {K L : CochainComplex Cᵒᵖ ℕ} {Z W : Cᵒᵖ}
  (ι : (CochainComplex.single₀ Cᵒᵖ).obj Z ⟶ K) (κ : (CochainComplex.single₀ Cᵒᵖ).obj W ⟶ L)
  [QuasiIso ι] [QuasiIso κ]
  (hK : ∀ a q, Subsingleton (Ext.{z} (K.X a).unop Y (q + 1)))
  (hL : ∀ a q, Subsingleton (Ext.{z} (L.X a).unop Y (q + 1)))
  (φ : K ⟶ L) (f : Z ⟶ W) (hφ : ι ≫ φ = (CochainComplex.single₀ Cᵒᵖ).map f ≫ κ)

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y 0

include hφ

theorem short_zero : ShortComplex.homologyMap ((F).mapShortComplex.map (Augmented.ResolutionCycleMaps.differential φ 0)) ≫
    (Resolution.Comparison.shortHomologyIso R Y L κ hL 0).hom =
      (Resolution.Comparison.shortHomologyIso R Y K ι hK 0).hom ≫
        (IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y 1).map f := by
  let : Subsingleton (Ext.{z} (K.X 0).unop Y 1) := hK 0 0
  let : Subsingleton (Ext.{z} (L.X 0).unop Y 1) := hL 0 0
  have h := HomologyNaturality.homology R Y
    (T := Augmented.ResolutionCycles.differentialSequence K 0) (U := Augmented.ResolutionCycles.differentialSequence L 0)
    (Augmented.ResolutionCycles.augmentation K ι) (Augmented.ResolutionCycles.augmentation L κ)
    (Augmented.ResolutionCycles.initialSequence K ι).zero (Augmented.ResolutionCycles.initialSequence L κ).zero
    (Augmented.ResolutionCycles.initialSequence_shortExact K ι) (Augmented.ResolutionCycles.initialSequence_shortExact L κ)
    (Augmented.ResolutionCycleMaps.differential φ 0) f (Augmented.ResolutionCycleMaps.augmentation φ ι κ f hφ)
  exact h

theorem short_succ (n : ℕ) : ShortComplex.homologyMap ((F).mapShortComplex.map (Augmented.ResolutionCycleMaps.differential φ (n + 1))) ≫
    (Resolution.Comparison.shortHomologyIso R Y L κ hL (n + 1)).hom =
      (Resolution.Comparison.shortHomologyIso R Y K ι hK (n + 1)).hom ≫
        (IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y (n + 1 + 1)).map f := by
  let : Subsingleton (Ext.{z} (K.X (n + 1)).unop Y 1) := hK (n + 1) 0
  let : Subsingleton (Ext.{z} (L.X (n + 1)).unop Y 1) := hL (n + 1) 0
  let eK := ResolutionShift.cycleExtEquiv R Y K ι hK n 0
  let eL := ResolutionShift.cycleExtEquiv R Y L κ hL n 0
  let hc : n + 0 + 2 = n + 1 + 1 := by omega
  have hs : (IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y 1).map (ShortComplex.cyclesMap (Augmented.ResolutionCycleMaps.differential φ n)) ≫
      (hc ▸ eL).toModuleIso.hom = (hc ▸ eK).toModuleIso.hom ≫
        (IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y (n + 1 + 1)).map f := by
    apply transport R Y f hc eK eL
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    exact ShiftNaturality.cycles R Y ι κ hK hL φ f hφ n 0 α
  have hd := HomologyNaturality.homology R Y
    (T := Augmented.ResolutionCycles.differentialSequence K (n + 1)) (U := Augmented.ResolutionCycles.differentialSequence L (n + 1))
    (Augmented.ResolutionCycles.differentialSequence K n).iCycles (Augmented.ResolutionCycles.differentialSequence L n).iCycles
    (Augmented.ResolutionCycles.successiveSequence K n).zero (Augmented.ResolutionCycles.successiveSequence L n).zero
    (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (Augmented.ResolutionCycles.successiveSequence_shortExact L κ n)
    (Augmented.ResolutionCycleMaps.differential φ (n + 1)) (ShortComplex.cyclesMap (Augmented.ResolutionCycleMaps.differential φ n))
    (ShortComplex.cyclesMap_i (Augmented.ResolutionCycleMaps.differential φ n))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (hc ▸ eL).toModuleIso.hom) hd).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun a =>
          (ResolutionHomologyData.homologyIso R Y (Augmented.ResolutionCycles.differentialSequence K (n + 1))
            (Augmented.ResolutionCycles.successiveSequence K n).f (Augmented.ResolutionCycles.successiveSequence K n).zero
            (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n)).hom ≫ a) hs).trans
              (Category.assoc _ _ _).symm)))

theorem short (n : ℕ) : ShortComplex.homologyMap ((F).mapShortComplex.map (Augmented.ResolutionCycleMaps.differential φ n)) ≫
    (Resolution.Comparison.shortHomologyIso R Y L κ hL n).hom =
      (Resolution.Comparison.shortHomologyIso R Y K ι hK n).hom ≫
        (IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y (n + 1)).map f := by
  cases n with
  | zero => exact short_zero R Y ι κ hK hL φ f hφ
  | succ n => exact short_succ R Y ι κ hK hL φ f hφ n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ShortNaturality.Comparison
