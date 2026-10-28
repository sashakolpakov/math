import OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution

/-! # Resolution Zero -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison

noncomputable section

/-!
# IntegralComparison: degree zero of the original-coefficient resolution comparison
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open Abelian OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionCycles

universe u v z t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{z} C]
  (R : Type t) [CommRing R] [Linear R C] (X : C)
  (K : CochainComplex C ℕ) {Z : C} (ι : (CochainComplex.single₀ C).obj Z ⟶ K) [QuasiIso ι]

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ModuleFunctor.functor R X 0
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.Resolution.Comparison.complex R X K

omit [QuasiIso ι] in
theorem augmentation_condition : (F).map (Augmented.ResolutionCycles.augmentation K ι) ≫ (L).d 0 1 = 0 :=
  ((F).map_comp _ _).symm.trans
    ((congrArg (F).map (Augmented.ResolutionCycles.augmentation_condition K ι)).trans ((F).map_zero _ _))

def augmentation : (CochainComplex.single₀ _).obj ((F).obj Z) ⟶ L :=
  (CochainComplex.fromSingle₀Equiv _ _).symm
    ⟨(F).map (Augmented.ResolutionCycles.augmentation K ι), augmentation_condition R X K ι⟩

omit [QuasiIso ι] in
theorem augmentation_zero : (augmentation R X K ι).f 0 = (F).map (Augmented.ResolutionCycles.augmentation K ι) :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

instance augmentation_quasiIsoAt_zero : QuasiIsoAt (augmentation R X K ι) 0 := by
  have h := Augmented.ResolutionCycles.augmentation_exact_and_mono K ι
  let : Mono (Augmented.ResolutionCycles.augmentation K ι) := h.2
  rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
  · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
      ⟨IntegralComparison.Ext.ZeroKernels.map_exact R X _ h.1,
        IntegralComparison.Ext.ZeroKernels.map_mono R X (Augmented.ResolutionCycles.augmentation K ι)⟩
    exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((Category.id_comp _).trans ((augmentation_zero R X K ι).symm.trans (Category.comp_id _).symm))
      ((Category.id_comp _).trans (Category.comp_id _).symm)
  all_goals first | rfl | exact (L).shape 0 0 (by simp)

def homologyIso : (L).homology 0 ≅ ModuleCat.of R (Ext.{z} X Z 0) :=
  (isoOfQuasiIsoAt (augmentation R X K ι) 0).symm ≪≫
    HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℕ) 0 ((F).obj Z)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Acyclic.ResolutionZero.Comparison
