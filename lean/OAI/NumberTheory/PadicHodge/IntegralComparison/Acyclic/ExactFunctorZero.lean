import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ExactFunctorComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero

/-! # Exact Functor Zero -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ExactFunctorZero

noncomputable section

/-! Exact functors respect degree zero of the original acyclic-resolution Ext comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R] (X : C)
  (K : CochainComplex C ℕ) {Z : C} (ι : (CochainComplex.single₀ C).obj Z ⟶ K)
  (κ : (CochainComplex.single₀ D).obj (F.obj Z) ⟶
    (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) (hκ : κ.f 0 = F.map (ι.f 0))
  [QuasiIso ι] [QuasiIso κ]

local notation "L" => Functor.obj (Functor.mapHomologicalComplex F (ComplexShape.up ℕ)) K
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.augmentation R X K ι
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.augmentation R (F.obj X) L κ
local notation "φ" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ExactFunctorComplex.map F R X K
local notation "η" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ExactFunctorModule.component F R X 0 Z

include hκ

omit [QuasiIso ι] [QuasiIso κ] in
theorem augmentation : a ≫ φ = (CochainComplex.single₀ _).map η ≫ b := by
  apply HomologicalComplex.from_single_hom_ext
  change (a).f 0 ≫ (φ).f 0 = ((CochainComplex.single₀ _).map η).f 0 ≫ (b).f 0
  rw [ResolutionZero.Comparison.augmentation_zero,
    ResolutionZero.Comparison.augmentation_zero, CochainComplex.single₀_map_f_zero]
  exact (Ext.ExactFunctorModule.naturality F R X 0 (ι.f 0)).trans
    (congrArg (fun f => η ≫ (Ext.ModuleFunctor.functor R (F.obj X) 0).map f) hκ.symm)

theorem homology : HomologicalComplex.homologyMap φ 0 ≫
    (ResolutionZero.Comparison.homologyIso R (F.obj X) L κ).hom =
      (ResolutionZero.Comparison.homologyIso R X K ι).hom ≫ η := by
  have h : HomologicalComplex.homologyMap a 0 ≫ HomologicalComplex.homologyMap φ 0 =
      HomologicalComplex.homologyMap ((CochainComplex.single₀ _).map η) 0 ≫
        HomologicalComplex.homologyMap b 0 :=
    (HomologicalComplex.homologyMap_comp a φ 0).symm.trans
      ((congrArg (fun f => HomologicalComplex.homologyMap f 0) (augmentation F R X K ι κ hκ)).trans
        (HomologicalComplex.homologyMap_comp _ _ 0))
  apply (cancel_epi (HomologicalComplex.homologyMap a 0)).mp
  change HomologicalComplex.homologyMap a 0 ≫
      (HomologicalComplex.homologyMap φ 0 ≫ ((isoOfQuasiIsoAt b 0).inv ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
          ((Ext.ModuleFunctor.functor R (F.obj X) 0).obj (F.obj Z))).hom)) =
    HomologicalComplex.homologyMap a 0 ≫ (((isoOfQuasiIsoAt a 0).inv ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
        ((Ext.ModuleFunctor.functor R X 0).obj Z)).hom) ≫ η)
  rw [← Category.assoc, h]
  simp only [Category.assoc, isoOfQuasiIsoAt_hom_inv_id_assoc]
  exact HomologicalComplex.singleObjHomologySelfIso_hom_naturality (ComplexShape.up ℕ) 0 η

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ExactFunctorZero
