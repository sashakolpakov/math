import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ExactFunctorComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionZero

/-! # Exact Functor Zero -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ExactFunctorZero

noncomputable section

/-! Exact functors respect degree zero of the original acyclic source-resolution Ext comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

attribute [local instance] preservesFiniteLimits_op preservesFiniteColimits_op

open Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R] (Y : C)
  (K : CochainComplex Cᵒᵖ ℕ) {Z : Cᵒᵖ} (ι : (CochainComplex.single₀ Cᵒᵖ).obj Z ⟶ K)
  (κ : (CochainComplex.single₀ Dᵒᵖ).obj (F.op.obj Z) ⟶
    (F.op.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) (hκ : κ.f 0 = F.op.map (ι.f 0))
  [QuasiIso ι] [QuasiIso κ]

local notation "L" => Functor.obj (Functor.mapHomologicalComplex F.op (ComplexShape.up ℕ)) K
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionZero.augmentation R Y K ι
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionZero.augmentation R (F.obj Y) L κ
local notation "φ" => OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ExactFunctorComplex.map F R Y K
local notation "η" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceExactFunctorModule.component F R Y 0 Z

include hκ

omit [QuasiIso ι] [QuasiIso κ] in
theorem augmentation : a ≫ φ = (CochainComplex.single₀ _).map η ≫ b := by
  apply HomologicalComplex.from_single_hom_ext
  change (a).f 0 ≫ (φ).f 0 = ((CochainComplex.single₀ _).map η).f 0 ≫ (b).f 0
  rw [ResolutionZero.augmentation_zero,
    ResolutionZero.augmentation_zero, CochainComplex.single₀_map_f_zero]
  exact (Ext.SourceExactFunctorModule.naturality F R Y 0 (ι.f 0)).trans
    (congrArg (fun f => η ≫ (Ext.ContravariantModuleFunctor.functor R (F.obj Y) 0).map f) hκ.symm)

theorem homology : HomologicalComplex.homologyMap φ 0 ≫
    (ResolutionZero.homologyIso R (F.obj Y) L κ).hom =
      (ResolutionZero.homologyIso R Y K ι).hom ≫ η := by
  have h : HomologicalComplex.homologyMap a 0 ≫ HomologicalComplex.homologyMap φ 0 =
      HomologicalComplex.homologyMap ((CochainComplex.single₀ _).map η) 0 ≫
        HomologicalComplex.homologyMap b 0 :=
    (HomologicalComplex.homologyMap_comp a φ 0).symm.trans
      ((congrArg (fun f => HomologicalComplex.homologyMap f 0) (augmentation F R Y K ι κ hκ)).trans
        (HomologicalComplex.homologyMap_comp _ _ 0))
  apply (cancel_epi (HomologicalComplex.homologyMap a 0)).mp
  change HomologicalComplex.homologyMap a 0 ≫
      (HomologicalComplex.homologyMap φ 0 ≫ ((isoOfQuasiIsoAt b 0).inv ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
          ((Ext.ContravariantModuleFunctor.functor R (F.obj Y) 0).obj (F.op.obj Z))).hom)) =
    HomologicalComplex.homologyMap a 0 ≫ (((isoOfQuasiIsoAt a 0).inv ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
        ((Ext.ContravariantModuleFunctor.functor R Y 0).obj Z)).hom) ≫ η)
  rw [← Category.assoc, h]
  simp only [Category.assoc, isoOfQuasiIsoAt_hom_inv_id_assoc]
  exact HomologicalComplex.singleObjHomologySelfIso_hom_naturality (ComplexShape.up ℕ) 0 η

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ExactFunctorZero
