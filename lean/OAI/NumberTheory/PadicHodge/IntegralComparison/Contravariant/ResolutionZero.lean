import OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.Resolution

/-! # Resolution Zero -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionZero

noncomputable section

/-!
# IntegralComparison: degree zero of the original source-resolution comparison
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

open Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (Y : C)
  (K : CochainComplex Cᵒᵖ ℕ) {Z : Cᵒᵖ} (ι : (CochainComplex.single₀ Cᵒᵖ).obj Z ⟶ K) [QuasiIso ι]

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ContravariantModuleFunctor.functor R Y 0
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.Resolution.Comparison.complex R Y K

omit [QuasiIso ι] in
theorem augmentation_condition : (F).map (Augmented.ResolutionCycles.augmentation K ι) ≫ (L).d 0 1 = 0 :=
  ((F).map_comp _ _).symm.trans
    ((congrArg (F).map (Augmented.ResolutionCycles.augmentation_condition K ι)).trans ((F).map_zero _ _))

def augmentation : (CochainComplex.single₀ _).obj ((F).obj Z) ⟶ L :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨(F).map (Augmented.ResolutionCycles.augmentation K ι), augmentation_condition R Y K ι⟩

omit [QuasiIso ι] in
theorem augmentation_zero : (augmentation R Y K ι).f 0 = (F).map (Augmented.ResolutionCycles.augmentation K ι) :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

instance augmentation_quasiIsoAt_zero : QuasiIsoAt (augmentation R Y K ι) 0 := by
  have h := Augmented.ResolutionCycles.augmentation_exact_and_mono K ι
  let : Mono (Augmented.ResolutionCycles.augmentation K ι) := h.2
  rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
  · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
      ⟨IntegralComparison.Ext.SourceZeroKernels.map_exact R Y _ h.1,
        IntegralComparison.Ext.SourceZeroKernels.map_mono R Y (Augmented.ResolutionCycles.augmentation K ι)⟩
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans ((augmentation_zero R Y K ι).symm.trans (Category.comp_id _).symm))
      ((Category.id_comp _).trans (Category.comp_id _).symm)
  all_goals first | rfl | exact (L).shape 0 0 (by simp)

def homologyIso : (L).homology 0 ≅ ModuleCat.of R (Ext.{z} Z.unop Y 0) :=
  (isoOfQuasiIsoAt (augmentation R Y K ι) 0).symm ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 ((F).obj Z)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Contravariant.ResolutionZero
