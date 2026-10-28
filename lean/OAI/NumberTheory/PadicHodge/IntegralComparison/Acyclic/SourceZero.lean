import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceModule
import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero

/-! # Source Zero -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.SourceZero

noncomputable section

/-! Degree zero of the actual acyclic-resolution comparison is natural in the first argument of Ext. -/

open _root_.CategoryTheory

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] {X X' : C} (f : X' ⟶ X)
  (K : CochainComplex C ℕ) {Z : C} (ι : (CochainComplex.single₀ C).obj Z ⟶ K)
  [QuasiIso ι]

local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.augmentation R X K ι
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison.augmentation R X' K ι
local notation "φ" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceModule.complexMap R f K
local notation "η" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceModule.component R f 0 Z

omit [QuasiIso ι] in
theorem augmentation : a ≫ φ = (CochainComplex.single₀ _).map η ≫ b := by
  apply HomologicalComplex.from_single_hom_ext
  change (a).f 0 ≫ (φ).f 0 = ((CochainComplex.single₀ _).map η).f 0 ≫ (b).f 0
  rw [ResolutionZero.Comparison.augmentation_zero,
    ResolutionZero.Comparison.augmentation_zero, CochainComplex.single₀_map_f_zero]
  exact Ext.SourceModule.naturality R f 0 (ι.f 0)

theorem homology : HomologicalComplex.homologyMap φ 0 ≫
    (ResolutionZero.Comparison.homologyIso R X' K ι).hom =
      (ResolutionZero.Comparison.homologyIso R X K ι).hom ≫ η := by
  have h : HomologicalComplex.homologyMap a 0 ≫ HomologicalComplex.homologyMap φ 0 =
      HomologicalComplex.homologyMap ((CochainComplex.single₀ _).map η) 0 ≫
        HomologicalComplex.homologyMap b 0 :=
    (HomologicalComplex.homologyMap_comp a φ 0).symm.trans
      ((congrArg (fun g => HomologicalComplex.homologyMap g 0) (augmentation R f K ι)).trans
        (HomologicalComplex.homologyMap_comp _ _ 0))
  apply (cancel_epi (HomologicalComplex.homologyMap a 0)).mp
  change HomologicalComplex.homologyMap a 0 ≫
      (HomologicalComplex.homologyMap φ 0 ≫ ((isoOfQuasiIsoAt b 0).inv ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
          ((Ext.ModuleFunctor.functor R X' 0).obj Z)).hom)) =
    HomologicalComplex.homologyMap a 0 ≫ (((isoOfQuasiIsoAt a 0).inv ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0
        ((Ext.ModuleFunctor.functor R X 0).obj Z)).hom) ≫ η)
  rw [← Category.assoc, h]
  simp only [Category.assoc, isoOfQuasiIsoAt_hom_inv_id_assoc]
  exact HomologicalComplex.singleObjHomologySelfIso_hom_naturality (ComplexShape.up ℕ) 0 η

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.SourceZero
