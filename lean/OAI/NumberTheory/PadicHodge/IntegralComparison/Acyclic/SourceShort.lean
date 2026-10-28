import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.SourceHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.SourceShift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution

/-! # Source Short -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.SourceShort

noncomputable section

/-! The original positive-degree Ext comparison on consecutive terms is natural in its source. -/

open _root_.CategoryTheory

open Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] {X X' : C} (f : X' ⟶ X)

private theorem transport {Z : C} {d d' : ℕ} (hd : d = d')
    {U V : Type z} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (e : U ≃ₗ[R] Ext.{z} X Z d) (e' : V ≃ₗ[R] Ext.{z} X' Z d)
    (a : ModuleCat.of R U ⟶ ModuleCat.of R V)
    (h : a ≫ e'.toModuleIso.hom = e.toModuleIso.hom ≫ IntegralComparison.Ext.SourceModule.component R f d Z) :
    a ≫ (hd ▸ e').toModuleIso.hom =
      (hd ▸ e).toModuleIso.hom ≫ IntegralComparison.Ext.SourceModule.component R f d' Z := by
  subst d'
  exact h

variable (K : CochainComplex C ℕ) {Z : C} (ι : (CochainComplex.single₀ C).obj Z ⟶ K)
  [QuasiIso ι]
  (hK : ∀ a q, Subsingleton (Ext.{z} X (K.X a) (q + 1)))
  (hK' : ∀ a q, Subsingleton (Ext.{z} X' (K.X a) (q + 1)))

theorem short_zero : ShortComplex.homologyMap (IntegralComparison.Ext.SourceModule.shortMap R f 0 (Augmented.ResolutionCycles.differentialSequence K 0)) ≫
    (Resolution.Comparison.shortHomologyIso R X' K ι hK' 0).hom =
      (Resolution.Comparison.shortHomologyIso R X K ι hK 0).hom ≫
        IntegralComparison.Ext.SourceModule.component R f 1 Z := by
  let : Subsingleton (Ext.{z} X (K.X 0) 1) := hK 0 0
  let : Subsingleton (Ext.{z} X' (K.X 0) 1) := hK' 0 0
  exact SourceHomology.homology R f (Augmented.ResolutionCycles.differentialSequence K 0)
    (Augmented.ResolutionCycles.augmentation K ι) (Augmented.ResolutionCycles.initialSequence K ι).zero (Augmented.ResolutionCycles.initialSequence_shortExact K ι)

theorem short_succ (n : ℕ) :
    ShortComplex.homologyMap (IntegralComparison.Ext.SourceModule.shortMap R f 0 (Augmented.ResolutionCycles.differentialSequence K (n + 1))) ≫
      (Resolution.Comparison.shortHomologyIso R X' K ι hK' (n + 1)).hom =
    (Resolution.Comparison.shortHomologyIso R X K ι hK (n + 1)).hom ≫
      IntegralComparison.Ext.SourceModule.component R f (n + 1 + 1) Z := by
  let : Subsingleton (Ext.{z} X (K.X (n + 1)) 1) := hK (n + 1) 0
  let : Subsingleton (Ext.{z} X' (K.X (n + 1)) 1) := hK' (n + 1) 0
  let eK := ResolutionShift.cycleExtEquiv R X K ι hK n 0
  let eK' := ResolutionShift.cycleExtEquiv R X' K ι hK' n 0
  let hc : n + 0 + 2 = n + 1 + 1 := by omega
  have hs : IntegralComparison.Ext.SourceModule.component R f 1 (Augmented.ResolutionCycles.differentialSequence K n).cycles ≫
      (hc ▸ eK').toModuleIso.hom = (hc ▸ eK).toModuleIso.hom ≫
        IntegralComparison.Ext.SourceModule.component R f (n + 1 + 1) Z := by
    apply transport R f hc eK eK'
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    exact SourceShift.cycles R f K ι hK hK' n 0 α
  have hd := SourceHomology.homology R f (Augmented.ResolutionCycles.differentialSequence K (n + 1))
    (Augmented.ResolutionCycles.differentialSequence K n).iCycles (Augmented.ResolutionCycles.successiveSequence K n).zero
    (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (hc ▸ eK').toModuleIso.hom) hd).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun a =>
          (ResolutionHomologyData.homologyIso R X (Augmented.ResolutionCycles.differentialSequence K (n + 1))
            (Augmented.ResolutionCycles.successiveSequence K n).f (Augmented.ResolutionCycles.successiveSequence K n).zero
            (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n)).hom ≫ a) hs).trans
              (Category.assoc _ _ _).symm)))

theorem short (n : ℕ) : ShortComplex.homologyMap (IntegralComparison.Ext.SourceModule.shortMap R f 0 (Augmented.ResolutionCycles.differentialSequence K n)) ≫
    (Resolution.Comparison.shortHomologyIso R X' K ι hK' n).hom =
      (Resolution.Comparison.shortHomologyIso R X K ι hK n).hom ≫
        IntegralComparison.Ext.SourceModule.component R f (n + 1) Z := by
  cases n with
  | zero => exact short_zero R f K ι hK hK'
  | succ n => exact short_succ R f K ι hK hK' n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.SourceShort
