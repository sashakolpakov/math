import OAI.NumberTheory.PadicHodge.IntegralComparison.MixedResolutionShort
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ExactFunctorComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionCohomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cochain.HomologyTripleNaturality

/-! # Mixed Resolution Cohomology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.MixedResolutionCohomology

noncomputable section

/-! Mixed naturality of the original Ext comparison, using acyclicity only
for the actual source and target resolutions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

attribute [local instance] preservesFiniteLimits_op preservesFiniteColimits_op

open Abelian

universe u v u' v' z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasExt.{z} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (R : Type t) [CommRing R] [Linear R C] [Linear R D] [F.Linear R] (Y : C)
  {K : CochainComplex Cᵒᵖ ℕ} {L : CochainComplex Dᵒᵖ ℕ}
  (φ : (F.op.mapHomologicalComplex (.up ℕ)).obj K ⟶ L)

local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ContravariantModuleFunctor.functor R (F.obj Y) 0

def map : Contravariant.Resolution.Comparison.complex R Y K ⟶
    Contravariant.Resolution.Comparison.complex R (F.obj Y) L :=
  Contravariant.ExactFunctorComplex.map F R Y K ≫ ((H).mapHomologicalComplex (.up ℕ)).map φ

theorem differential (n : ℕ) : Augmented.ResolutionCycleMaps.differential (MixedResolutionCohomology.map F R Y φ) n =
    Contravariant.ExactFunctorHomology.shortMap F R Y
      (Mapped.AugmentedCycleMaps.differential F.op φ n) := rfl

variable {Z : Cᵒᵖ} {W : Dᵒᵖ} (ι : (CochainComplex.single₀ Cᵒᵖ).obj Z ⟶ K)
  (κ : (CochainComplex.single₀ Dᵒᵖ).obj W ⟶ L) (g : F.op.obj Z ⟶ W)
  (h : g ≫ κ.f 0 = F.op.map (ι.f 0) ≫ φ.f 0)
  [QuasiIso ι] [QuasiIso κ]

local notation "augP" => OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionZero.augmentation R Y K ι
local notation "augQ" => OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionZero.augmentation R (F.obj Y) L κ
local notation "μ" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.SourceExactFunctorModule.component F R Y 0 Z ≫ CategoryTheory.Functor.map H g

include h

omit [QuasiIso ι] [QuasiIso κ] in
theorem augmentation : augP ≫ MixedResolutionCohomology.map F R Y φ = (CochainComplex.single₀ _).map μ ≫ augQ := by
  apply HomologicalComplex.from_single_hom_ext
  change (augP).f 0 ≫ (MixedResolutionCohomology.map F R Y φ).f 0 = ((CochainComplex.single₀ _).map μ).f 0 ≫ (augQ).f 0
  rw [Contravariant.ResolutionZero.augmentation_zero,
    Contravariant.ResolutionZero.augmentation_zero, CochainComplex.single₀_map_f_zero]
  change (IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y 0).map (ι.f 0) ≫
    (IntegralComparison.Ext.SourceExactFunctorModule.component F R Y 0 (K.X 0) ≫ (H).map (φ.f 0)) =
      (IntegralComparison.Ext.SourceExactFunctorModule.component F R Y 0 Z ≫ CategoryTheory.Functor.map H g) ≫ (H).map (κ.f 0)
  have hn : (IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y 0).map (ι.f 0) ≫
      IntegralComparison.Ext.SourceExactFunctorModule.component F R Y 0 (K.X 0) =
    IntegralComparison.Ext.SourceExactFunctorModule.component F R Y 0 Z ≫ (H).map (F.op.map (ι.f 0)) :=
      IntegralComparison.Ext.SourceExactFunctorModule.naturality F R Y 0 (ι.f 0)
  have hm : (H).map (F.op.map (ι.f 0)) ≫ (H).map (φ.f 0) =
      (H).map g ≫ (H).map (κ.f 0) :=
    ((H).map_comp (F.op.map (ι.f 0)) (φ.f 0)).symm.trans
      ((congrArg (H).map h.symm).trans ((H).map_comp g (κ.f 0)))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (H).map (φ.f 0)) hn).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun a => IntegralComparison.Ext.SourceExactFunctorModule.component F R Y 0 Z ≫ a) hm).trans
          (Category.assoc _ _ _).symm)))

theorem zero : HomologicalComplex.homologyMap (MixedResolutionCohomology.map F R Y φ) 0 ≫
    (Contravariant.ResolutionZero.homologyIso R (F.obj Y) L κ).hom =
      (Contravariant.ResolutionZero.homologyIso R Y K ι).hom ≫ μ := by
  have hs : HomologicalComplex.homologyMap augP 0 ≫ HomologicalComplex.homologyMap (MixedResolutionCohomology.map F R Y φ) 0 =
      HomologicalComplex.homologyMap ((CochainComplex.single₀ _).map μ) 0 ≫
        HomologicalComplex.homologyMap augQ 0 :=
    (HomologicalComplex.homologyMap_comp augP (MixedResolutionCohomology.map F R Y φ) 0).symm.trans
      ((congrArg (fun f => HomologicalComplex.homologyMap f 0) (augmentation F R Y φ ι κ g h)).trans
        (HomologicalComplex.homologyMap_comp _ _ 0))
  apply (cancel_epi (HomologicalComplex.homologyMap augP 0)).mp
  change HomologicalComplex.homologyMap augP 0 ≫
      (HomologicalComplex.homologyMap (MixedResolutionCohomology.map F R Y φ) 0 ≫ ((isoOfQuasiIsoAt augQ 0).inv ≫
        (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) 0 ((H).obj W)).hom)) =
    HomologicalComplex.homologyMap augP 0 ≫ (((isoOfQuasiIsoAt augP 0).inv ≫
      (HomologicalComplex.singleObjHomologySelfIso (.up ℕ) 0
        ((IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y 0).obj Z)).hom) ≫ μ)
  rw [← Category.assoc, hs]
  simp only [Category.assoc, isoOfQuasiIsoAt_hom_inv_id_assoc]
  exact HomologicalComplex.singleObjHomologySelfIso_hom_naturality (.up ℕ) 0 μ

variable (hK : ∀ a q, Subsingleton (Ext.{z} (K.X a).unop Y (q + 1)))
  (hL : ∀ a q, Subsingleton (Ext.{z} (L.X a).unop (F.obj Y) (q + 1)))

theorem positive (n : ℕ) : HomologicalComplex.homologyMap (MixedResolutionCohomology.map F R Y φ) (n + 1) ≫
    (Contravariant.Resolution.Comparison.positiveHomologyIso R (F.obj Y) L κ hL n).hom =
      (Contravariant.Resolution.Comparison.positiveHomologyIso R Y K ι hK n).hom ≫
        (IntegralComparison.Ext.SourceExactFunctorModule.component F R Y (n + 1) Z ≫
          (IntegralComparison.Ext.ContravariantModuleFunctor.functor R (F.obj Y) (n + 1)).map g) := by
  have h₁ := Cochain.HomologyTripleNaturality.naturality (MixedResolutionCohomology.map F R Y φ) n
  have h₂ := MixedResolutionShort.Comparison.short F R Y φ ι κ g h hK hL n
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (Contravariant.Resolution.Comparison.shortHomologyIso R (F.obj Y) L κ hL n).hom) h₁).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun a =>
          ((Contravariant.Resolution.Comparison.complex R Y K).homologyIsoSc' n (n + 1) (n + 2)
            (by simp) (by simp)).hom ≫ a) h₂).trans (Category.assoc _ _ _).symm)))

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (MixedResolutionCohomology.map F R Y φ) i ≫
    (Contravariant.ResolutionCohomology.homologyIso R (F.obj Y) L κ hL i).hom =
      (Contravariant.ResolutionCohomology.homologyIso R Y K ι hK i).hom ≫
        (IntegralComparison.Ext.SourceExactFunctorModule.component F R Y i Z ≫
          (IntegralComparison.Ext.ContravariantModuleFunctor.functor R (F.obj Y) i).map g) := by
  cases i with
  | zero => exact MixedResolutionCohomology.zero F R Y φ ι κ g h
  | succ i => exact positive F R Y φ ι κ g h hK hL i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.MixedResolutionCohomology
