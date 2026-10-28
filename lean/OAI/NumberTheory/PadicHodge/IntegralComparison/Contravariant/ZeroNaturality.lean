import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycleMaps

/-! # Zero Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ZeroNaturality

noncomputable section

/-! Degree zero of the original resolution comparison respects maps of augmented resolutions. -/

open _root_.CategoryTheory

open Abelian

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (Y : C)
  {K L : CochainComplex Cᵒᵖ ℕ} {Z W : Cᵒᵖ}
  (ι : (CochainComplex.single₀ Cᵒᵖ).obj Z ⟶ K) (κ : (CochainComplex.single₀ Cᵒᵖ).obj W ⟶ L)
  (φ : K ⟶ L) (f : Z ⟶ W) (hφ : ι ≫ φ = (CochainComplex.single₀ Cᵒᵖ).map f ≫ κ)
  [QuasiIso ι] [QuasiIso κ]

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y 0
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionZero.augmentation R Y K ι
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionZero.augmentation R Y L κ
local notation "ψ" => CategoryTheory.Functor.map (Functor.mapHomologicalComplex G (ComplexShape.up ℕ)) φ
local notation "η" => CategoryTheory.Functor.map G f

include hφ

omit [QuasiIso ι] [QuasiIso κ] in
theorem augmentation : a ≫ ψ = (CochainComplex.single₀ _).map η ≫ b := by
  apply HomologicalComplex.from_single_hom_ext
  change (a).f 0 ≫ (ψ).f 0 = ((CochainComplex.single₀ _).map η).f 0 ≫ (b).f 0
  rw [ResolutionZero.augmentation_zero,
    ResolutionZero.augmentation_zero, CochainComplex.single₀_map_f_zero]
  exact ((G).map_comp (ι.f 0) (φ.f 0)).symm.trans
    ((congrArg (G).map (Augmented.ResolutionCycleMaps.augmentation φ ι κ f hφ).symm).trans
      ((G).map_comp f (κ.f 0)))

theorem homology : HomologicalComplex.homologyMap ψ 0 ≫
    (ResolutionZero.homologyIso R Y L κ).hom =
      (ResolutionZero.homologyIso R Y K ι).hom ≫ η := by
  have h : HomologicalComplex.homologyMap a 0 ≫ HomologicalComplex.homologyMap ψ 0 =
      HomologicalComplex.homologyMap ((CochainComplex.single₀ _).map η) 0 ≫
        HomologicalComplex.homologyMap b 0 :=
    (HomologicalComplex.homologyMap_comp a ψ 0).symm.trans
      ((congrArg (fun g => HomologicalComplex.homologyMap g 0) (augmentation R Y ι κ φ f hφ)).trans
        (HomologicalComplex.homologyMap_comp _ _ 0))
  apply (cancel_epi (HomologicalComplex.homologyMap a 0)).mp
  change HomologicalComplex.homologyMap a 0 ≫
      (HomologicalComplex.homologyMap ψ 0 ≫ ((isoOfQuasiIsoAt b 0).inv ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 ((G).obj W)).hom)) =
    HomologicalComplex.homologyMap a 0 ≫ (((isoOfQuasiIsoAt a 0).inv ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 ((G).obj Z)).hom) ≫ η)
  have ht := congrArg (fun g => g ≫ (isoOfQuasiIsoAt b 0).inv ≫
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 ((G).obj W)).hom) h
  simp only [Category.assoc, isoOfQuasiIsoAt_hom_inv_id_assoc] at ht ⊢
  exact ht.trans (HomologicalComplex.singleObjHomologySelfIso_hom_naturality (ComplexShape.up ℕ) 0 η)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ZeroNaturality
