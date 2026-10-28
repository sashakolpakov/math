import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ExactFunctorHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ExactFunctorShift
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.Resolution

/-! # Exact Functor Short -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ExactFunctorShort

noncomputable section

/-! Exact functors preserve the original positive-degree Ext comparison on consecutive terms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

attribute [local instance] preservesFiniteLimits_op preservesFiniteColimits_op

open Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R] (Y : C)

private theorem transport {Z : Cᵒᵖ} {d d' : ℕ} (hd : d = d')
    {U V : Type z} [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    (e : U ≃ₗ[R] Ext.{z} Z.unop Y d) (e' : V ≃ₗ[R] Ext.{z} (F.op.obj Z).unop (F.obj Y) d)
    (a : ModuleCat.of R U ⟶ ModuleCat.of R V)
    (h : a ≫ e'.toModuleIso.hom = e.toModuleIso.hom ≫ IntegralComparison.Ext.SourceExactFunctorModule.component F R Y d Z) :
    a ≫ (hd ▸ e').toModuleIso.hom =
      (hd ▸ e).toModuleIso.hom ≫ IntegralComparison.Ext.SourceExactFunctorModule.component F R Y d' Z := by
  subst d'
  exact h

variable (K : CochainComplex Cᵒᵖ ℕ) {Z : Cᵒᵖ} (ι : (CochainComplex.single₀ Cᵒᵖ).obj Z ⟶ K)
  (κ : (CochainComplex.single₀ Dᵒᵖ).obj (F.op.obj Z) ⟶
    (F.op.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) (hκ : κ.f 0 = F.op.map (ι.f 0))
  [QuasiIso ι] [QuasiIso κ]
  (hK : ∀ a q, Subsingleton (Ext.{z} (K.X a).unop Y (q + 1)))
  (hL : ∀ a q, Subsingleton (Ext.{z} (((F.op.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).X a).unop (F.obj Y) (q + 1)))

local notation "L" => Functor.obj (Functor.mapHomologicalComplex F.op (ComplexShape.up ℕ)) K

include hκ

theorem short_zero : ShortComplex.homologyMap
    (IntegralComparison.Ext.SourceExactFunctorModule.shortMap F R Y 0 (Augmented.ResolutionCycles.differentialSequence K 0)) ≫
    (Resolution.Comparison.shortHomologyIso R (F.obj Y) L κ hL 0).hom =
      (Resolution.Comparison.shortHomologyIso R Y K ι hK 0).hom ≫
        IntegralComparison.Ext.SourceExactFunctorModule.component F R Y 1 Z := by
  let : Subsingleton (Ext.{z} (K.X 0).unop Y 1) := hK 0 0
  let : Subsingleton (Ext.{z} ((L).X 0).unop (F.obj Y) 1) := hL 0 0
  let : Subsingleton (Ext.{z} ((Augmented.ResolutionCycles.differentialSequence K 0).map F.op).X₁.unop (F.obj Y) 1) := hL 0 0
  have h := ExactFunctorHomology.homology F R Y (𝟙 ((Augmented.ResolutionCycles.differentialSequence K 0).map F.op))
    (Augmented.ResolutionCycles.augmentation K ι) (Augmented.ResolutionCycles.augmentation L κ) (Augmented.ResolutionCycles.initialSequence K ι).zero (Augmented.ResolutionCycles.initialSequence L κ).zero
    (Augmented.ResolutionCycles.initialSequence_shortExact K ι) (Augmented.ResolutionCycles.initialSequence_shortExact L κ) (𝟙 (F.op.obj Z))
    ((Category.id_comp _).trans (hκ.trans (Category.comp_id _).symm))
  rw [ExactFunctorHomology.shortMap_id] at h
  exact h.trans (congrArg (fun a =>
    (Resolution.Comparison.shortHomologyIso R Y K ι hK 0).hom ≫ a)
      ((congrArg (fun a => IntegralComparison.Ext.SourceExactFunctorModule.component F R Y 1 Z ≫ a)
        ((IntegralComparison.Ext.ContravariantModuleFunctor.functor R (F.obj Y) 1).map_id (F.op.obj Z))).trans (Category.comp_id _)))

theorem short_succ (n : ℕ) : ShortComplex.homologyMap
    (IntegralComparison.Ext.SourceExactFunctorModule.shortMap F R Y 0 (Augmented.ResolutionCycles.differentialSequence K (n + 1))) ≫
    (Resolution.Comparison.shortHomologyIso R (F.obj Y) L κ hL (n + 1)).hom =
      (Resolution.Comparison.shortHomologyIso R Y K ι hK (n + 1)).hom ≫
        IntegralComparison.Ext.SourceExactFunctorModule.component F R Y (n + 1 + 1) Z := by
  let : Subsingleton (Ext.{z} (K.X (n + 1)).unop Y 1) := hK (n + 1) 0
  let : Subsingleton (Ext.{z} ((L).X (n + 1)).unop (F.obj Y) 1) := hL (n + 1) 0
  let : Subsingleton (Ext.{z} ((Augmented.ResolutionCycles.differentialSequence K (n + 1)).map F.op).X₁.unop (F.obj Y) 1) := hL (n + 1) 0
  let eK := ResolutionShift.cycleExtEquiv R Y K ι hK n 0
  let eL := ResolutionShift.cycleExtEquiv R (F.obj Y) L κ hL n 0
  let hc : n + 0 + 2 = n + 1 + 1 := by omega
  let a := IntegralComparison.Ext.SourceExactFunctorModule.component F R Y 1 (Augmented.ResolutionCycles.differentialSequence K n).cycles ≫
    (IntegralComparison.Ext.ContravariantModuleFunctor.functor R (F.obj Y) 1).map (Augmented.CyclesExactFunctor.cyclesIso F.op K n).hom
  have hs : a ≫ (hc ▸ eL).toModuleIso.hom =
      (hc ▸ eK).toModuleIso.hom ≫ IntegralComparison.Ext.SourceExactFunctorModule.component F R Y (n + 1 + 1) Z := by
    apply transport F R Y hc eK eL
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    exact ExactFunctorShift.cycles F R Y K ι κ hκ hK hL n 0 α
  have hd := ExactFunctorHomology.homology F R Y
    (𝟙 ((Augmented.ResolutionCycles.differentialSequence K (n + 1)).map F.op))
    (Augmented.ResolutionCycles.differentialSequence K n).iCycles (Augmented.ResolutionCycles.differentialSequence L n).iCycles
    (Augmented.ResolutionCycles.successiveSequence K n).zero (Augmented.ResolutionCycles.successiveSequence L n).zero
    (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n) (Augmented.ResolutionCycles.successiveSequence_shortExact L κ n)
    (Augmented.CyclesExactFunctor.cyclesIso F.op K n).hom
    ((Augmented.CyclesExactFunctor.cycles_i F.op K n).trans (Category.comp_id _).symm)
  rw [ExactFunctorHomology.shortMap_id] at hd
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun b => b ≫ (hc ▸ eL).toModuleIso.hom) hd).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun b =>
          (ResolutionHomologyData.homologyIso R Y (Augmented.ResolutionCycles.differentialSequence K (n + 1))
            (Augmented.ResolutionCycles.successiveSequence K n).f (Augmented.ResolutionCycles.successiveSequence K n).zero
            (Augmented.ResolutionCycles.successiveSequence_shortExact K ι n)).hom ≫ b) hs).trans
              (Category.assoc _ _ _).symm)))

theorem short (n : ℕ) : ShortComplex.homologyMap
    (IntegralComparison.Ext.SourceExactFunctorModule.shortMap F R Y 0 (Augmented.ResolutionCycles.differentialSequence K n)) ≫
    (Resolution.Comparison.shortHomologyIso R (F.obj Y) L κ hL n).hom =
      (Resolution.Comparison.shortHomologyIso R Y K ι hK n).hom ≫
        IntegralComparison.Ext.SourceExactFunctorModule.component F R Y (n + 1) Z := by
  cases n with
  | zero => exact short_zero F R Y K ι κ hκ hK hL
  | succ n => exact short_succ F R Y K ι κ hκ hK hL n

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ExactFunctorShort
