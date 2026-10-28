import Mathlib

/-! # Left Exact Resolution -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LeftExactResolution

noncomputable section

/-!
# IntegralComparison: mapping an injective resolution through a left exact functor

This construction requires exactness of the particular mapped complex
in positive degrees. It does not assume that the functor is exact.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe v v' u u'

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [F.PreservesInjectiveObjects]
  {Z : C} (I : InjectiveResolution Z)

def complex : CochainComplex D ℕ := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex

omit [PreservesFiniteLimits F] [F.PreservesInjectiveObjects] in
theorem augmentation_condition : F.map (I.ι.f 0) ≫ (complex F I).d 0 1 = 0 := by
  change F.map (I.ι.f 0) ≫ F.map (I.cocomplex.d 0 1) = 0
  rw [← F.map_comp, I.ι_f_zero_comp_complex_d, F.map_zero]

def augmentation : (CochainComplex.single₀ D).obj (F.obj Z) ⟶ complex F I :=
  (CochainComplex.fromSingle₀Equiv _ _).symm ⟨F.map (I.ι.f 0), augmentation_condition F I⟩

omit [F.PreservesInjectiveObjects] in
theorem augmentation_exact :
    (ShortComplex.mk (F.map (I.ι.f 0)) ((complex F I).d 0 1) (augmentation_condition F I)).Exact :=
  ShortComplex.exact_of_f_is_kernel _ (KernelFork.mapIsLimit _ I.isLimitKernelFork F)

omit [PreservesFiniteLimits F] [F.PreservesInjectiveObjects] in
theorem augmentation_zero : (augmentation F I).f 0 = F.map (I.ι.f 0) :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

def resolution (h : ∀ n, (complex F I).ExactAt (n + 1)) : InjectiveResolution (F.obj Z) where
  cocomplex := complex F I
  injective n := F.injective_obj_of_injective (I.injective n)
  ι := augmentation F I
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros]
      · refine (ShortComplex.exact_and_mono_f_iff_of_iso ?_).2
          ⟨augmentation_exact F I, inferInstance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          ((Category.id_comp _).trans ((augmentation_zero F I).symm.trans (Category.comp_id _).symm))
          ((Category.id_comp _).trans (Category.comp_id _).symm)
      all_goals first | rfl | exact (complex F I).shape 0 0 (by simp)
    | succ n =>
      exact (quasiIsoAt_iff_exactAt _ (n + 1) (CochainComplex.exactAt_succ_single_obj _ _)).mpr (h n)⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LeftExactResolution
