import OAI.NumberTheory.PadicHodge.IntegralComparison.MixedResolutionDimensionShift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ExactFunctorHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.Resolution

/-! # Mixed Resolution Short -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.MixedResolutionShort

noncomputable section

/-! The native Ext comparison on consecutive terms is natural for a mixed
map of augmented source resolutions; no intermediate acyclicity is used. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

attribute [local instance] preservesFiniteLimits_op preservesFiniteColimits_op

namespace Comparison

open Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R] (Y : C)

private theorem transport {Z : Cᵒᵖ} {W : Dᵒᵖ} (g : F.op.obj Z ⟶ W) {d d' : ℕ} (hd : d = d')
    {U V : Type z} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (e : U ≃ₗ[R] Ext.{z} Z.unop Y d) (e' : V ≃ₗ[R] Ext.{z} W.unop (F.obj Y) d)
    (a : ModuleCat.of R U ⟶ ModuleCat.of R V)
    (h : a ≫ e'.toModuleIso.hom = e.toModuleIso.hom ≫
      (IntegralComparison.Ext.SourceExactFunctorModule.component F R Y d Z ≫
        (IntegralComparison.Ext.ContravariantModuleFunctor.functor R (F.obj Y) d).map g)) :
    a ≫ (hd ▸ e').toModuleIso.hom = (hd ▸ e).toModuleIso.hom ≫
      (IntegralComparison.Ext.SourceExactFunctorModule.component F R Y d' Z ≫
        (IntegralComparison.Ext.ContravariantModuleFunctor.functor R (F.obj Y) d').map g) := by
  subst d'
  exact h

variable {K : CochainComplex Cᵒᵖ ℕ} {L : CochainComplex Dᵒᵖ ℕ}
  (φ : (F.op.mapHomologicalComplex (.up ℕ)).obj K ⟶ L)
  {Z : Cᵒᵖ} {W : Dᵒᵖ} (ι : (CochainComplex.single₀ Cᵒᵖ).obj Z ⟶ K)
  (κ : (CochainComplex.single₀ Dᵒᵖ).obj W ⟶ L) (g : F.op.obj Z ⟶ W)
  (h : g ≫ κ.f 0 = F.op.map (ι.f 0) ≫ φ.f 0)
  [QuasiIso ι] [QuasiIso κ]
  (hK : ∀ a q, Subsingleton (Ext.{z} (K.X a).unop Y (q + 1)))
  (hL : ∀ a q, Subsingleton (Ext.{z} (L.X a).unop (F.obj Y) (q + 1)))

include h

theorem short_zero : ShortComplex.homologyMap
    (Contravariant.ExactFunctorHomology.shortMap F R Y (Mapped.AugmentedCycleMaps.differential F.op φ 0)) ≫
      (Contravariant.Resolution.Comparison.shortHomologyIso R (F.obj Y) L κ hL 0).hom =
        (Contravariant.Resolution.Comparison.shortHomologyIso R Y K ι hK 0).hom ≫
          (IntegralComparison.Ext.SourceExactFunctorModule.component F R Y 1 Z ≫
            (IntegralComparison.Ext.ContravariantModuleFunctor.functor R (F.obj Y) 1).map g) := by
  let : Subsingleton (Ext.{z} (K.X 0).unop Y 1) := hK 0 0
  let : Subsingleton (Ext.{z} (L.X 0).unop (F.obj Y) 1) := hL 0 0
  exact Contravariant.ExactFunctorHomology.homology F R Y
    (Mapped.AugmentedCycleMaps.differential F.op φ 0)
    (Augmented.ResolutionCycles.augmentation K ι) (Augmented.ResolutionCycles.augmentation L κ) (Augmented.ResolutionCycles.initialSequence K ι).zero (Augmented.ResolutionCycles.initialSequence L κ).zero
    (Augmented.ResolutionCycles.initialSequence_shortExact K ι) (Augmented.ResolutionCycles.initialSequence_shortExact L κ) g h

theorem short_succ (n : ℕ) : ShortComplex.homologyMap
    (Contravariant.ExactFunctorHomology.shortMap F R Y (Mapped.AugmentedCycleMaps.differential F.op φ (n + 1))) ≫
      (Contravariant.Resolution.Comparison.shortHomologyIso R (F.obj Y) L κ hL (n + 1)).hom =
        (Contravariant.Resolution.Comparison.shortHomologyIso R Y K ι hK (n + 1)).hom ≫
          (IntegralComparison.Ext.SourceExactFunctorModule.component F R Y (n + 1 + 1) Z ≫
            (IntegralComparison.Ext.ContravariantModuleFunctor.functor R (F.obj Y) (n + 1 + 1)).map g) := by
  let : Subsingleton (Ext.{z} (K.X (n + 1)).unop Y 1) := hK (n + 1) 0
  let : Subsingleton (Ext.{z} (L.X (n + 1)).unop (F.obj Y) 1) := hL (n + 1) 0
  let eK := Contravariant.ResolutionShift.cycleExtEquiv R Y K ι hK n 0
  let eL := Contravariant.ResolutionShift.cycleExtEquiv R (F.obj Y) L κ hL n 0
  let hc : n + 0 + 2 = n + 1 + 1 := by omega
  let a := IntegralComparison.Ext.SourceExactFunctorModule.component F R Y 1 (Augmented.ResolutionCycles.differentialSequence K n).cycles ≫
    (IntegralComparison.Ext.ContravariantModuleFunctor.functor R (F.obj Y) 1).map (Mapped.AugmentedCycleMaps.cycles F.op φ n)
  have hs : a ≫ (hc ▸ eL).toModuleIso.hom =
      (hc ▸ eK).toModuleIso.hom ≫ (IntegralComparison.Ext.SourceExactFunctorModule.component F R Y (n + 1 + 1) Z ≫
        (IntegralComparison.Ext.ContravariantModuleFunctor.functor R (F.obj Y) (n + 1 + 1)).map g) := by
    apply transport F R Y g hc eK eL
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    exact MixedResolutionDimensionShift.cycles F R Y φ ι κ g h hK hL n 0 α
  have hd := Contravariant.ExactFunctorHomology.homology F R Y
    (Mapped.AugmentedCycleMaps.differential F.op φ (n + 1))
    (Augmented.ResolutionCycles.differentialSequence K n).iCycles (Augmented.ResolutionCycles.differentialSequence L n).iCycles
    (Augmented.ResolutionCycles.successiveSequence K n).zero (Augmented.ResolutionCycles.successiveSequence L n).zero
    (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (Augmented.ResolutionCycles.successiveSequence_shortExact L κ n)
    (Mapped.AugmentedCycleMaps.cycles F.op φ n) (Mapped.AugmentedCycleMaps.cycles_i F.op φ n)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun b => b ≫ (hc ▸ eL).toModuleIso.hom) hd).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun b =>
          (Contravariant.ResolutionHomologyData.homologyIso R Y (Augmented.ResolutionCycles.differentialSequence K (n + 1))
            (Augmented.ResolutionCycles.successiveSequence K n).f (Augmented.ResolutionCycles.successiveSequence K n).zero
            (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n)).hom ≫ b) hs).trans
              (Category.assoc _ _ _).symm)))

theorem short (n : ℕ) : ShortComplex.homologyMap
    (Contravariant.ExactFunctorHomology.shortMap F R Y (Mapped.AugmentedCycleMaps.differential F.op φ n)) ≫
      (Contravariant.Resolution.Comparison.shortHomologyIso R (F.obj Y) L κ hL n).hom =
        (Contravariant.Resolution.Comparison.shortHomologyIso R Y K ι hK n).hom ≫
          (IntegralComparison.Ext.SourceExactFunctorModule.component F R Y (n + 1) Z ≫
            (IntegralComparison.Ext.ContravariantModuleFunctor.functor R (F.obj Y) (n + 1)).map g) := by
  cases n with
  | zero => exact short_zero F R Y φ ι κ g h hK hL
  | succ n => exact short_succ F R Y φ ι κ g h hK hL n

end Comparison

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.MixedResolutionShort
