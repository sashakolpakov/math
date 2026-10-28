import OAI.NumberTheory.PadicHodge.IntegralComparison.RegularElementKoszul
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.RingTheory.Finiteness.Prod

/-! # Regular Sequence Koszul -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RegularSequenceKoszul

noncomputable section

/-! The actual finite Koszul complex of a weakly regular sequence resolves
the original module quotient. Its construction uses scalar mapping cones. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Pointwise

open OAI.NumberTheory.PadicHodge.IntegralComparison.RegularElementKoszul

universe u
variable {R : Type u} [CommRing R]

def complex (M : ModuleCat.{u} R) (rs : List R) : CochainComplex (ModuleCat.{u} R) ℤ :=
  rs.foldl (fun K r => CochainComplex.mappingCone (RegularElementKoszul.scalar K r)) (RegularElementKoszul.single.obj M)

@[simp] theorem complex_nil (M : ModuleCat.{u} R) : complex M [] = RegularElementKoszul.single.obj M := rfl

theorem complex_append_singleton (M : ModuleCat.{u} R) (rs : List R) (r : R) :
    complex M (rs ++ [r]) = CochainComplex.mappingCone (RegularElementKoszul.scalar (complex M rs) r) := by
  simp only [complex, List.foldl_append, List.foldl_cons, List.foldl_nil]

abbrev quotient (M : ModuleCat.{u} R) (rs : List R) :=
  ModuleCat.of R (M ⧸ (Ideal.ofList rs • (⊤ : Submodule R M)))

def quotientNilIso (M : ModuleCat.{u} R) : quotient M [] ≅ M :=
  (Submodule.quotEquivOfEqBot _ (by simp)).toModuleIso

def quotientAppendIso (M : ModuleCat.{u} R) (rs : List R) (r : R) :
    quotient M (rs ++ [r]) ≅ ModuleCat.of R (QuotSMulTop r (quotient M rs)) :=
  ((Submodule.quotEquivOfEq _ _ (by
    simp only [Ideal.ofList_append, Ideal.ofList_cons, Ideal.ofList_nil, sup_bot_eq]
    rw [sup_comm])) ≪≫ₗ
      Submodule.quotOfListConsSMulTopEquivQuotSMulTopOuter M r rs).toModuleIso

theorem exists_augmentation (M : ModuleCat.{u} R) (rs : List R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular M rs) :
    ∃ ε : complex M rs ⟶ RegularElementKoszul.single.obj (quotient M rs), QuasiIso ε := by
  induction rs using List.reverseRecOn with
  | nil =>
    exact ⟨RegularElementKoszul.single.map (quotientNilIso M).inv, inferInstance⟩
  | append_singleton rs r ih =>
    obtain ⟨hprev, hlast⟩ := (RingTheory.Sequence.isWeaklyRegular_append_iff M rs [r]).mp hreg
    have hr := (RingTheory.Sequence.isWeaklyRegular_singleton_iff (quotient M rs) r).mp hlast
    obtain ⟨ε, hε⟩ := ih hprev
    rw [complex_append_singleton]
    let a := RegularElementKoszul.stepAugmentation (quotient M rs) ε r ≫ RegularElementKoszul.single.map (quotientAppendIso M rs r).inv
    have := RegularElementKoszul.stepAugmentation_quasiIso (quotient M rs) ε hε r hr
    exact ⟨a, quasiIso_comp _ _⟩

theorem term_isZero (M : ModuleCat.{u} R) (rs : List R) (i : ℤ)
    (hi : i < -(rs.length : ℤ) ∨ 0 < i) : IsZero ((complex M rs).X i) := by
  induction rs using List.reverseRecOn generalizing i with
  | nil =>
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i (by
      simp only [List.length_nil, Nat.cast_zero, neg_zero] at hi
      omega)
  | append_singleton rs r ih =>
    rw [complex_append_singleton]
    apply (CochainComplex.mappingCone.isZero_X_iff _ _).mpr
    simp only [List.length_append, List.length_singleton, Nat.cast_add, Nat.cast_one] at hi
    exact ⟨ih (i + 1) (by omega), ih i (by omega)⟩

def stepTermIso (K : CochainComplex (ModuleCat.{u} R) ℤ) (r : R) (i : ℤ) :
    (CochainComplex.mappingCone (RegularElementKoszul.scalar K r)).X i ≅ ModuleCat.of R (K.X (i + 1) × K.X i) :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod (RegularElementKoszul.scalar K r) i (i + 1) rfl ≪≫
    ModuleCat.biprodIsoProd _ _

theorem term_free (M : ModuleCat.{u} R) [Module.Free R M] (rs : List R) (i : ℤ) :
    Module.Free R ((complex M rs).X i) := by
  induction rs using List.reverseRecOn generalizing i with
  | nil =>
    by_cases hi : i = 0
    · subst i
      exact Module.Free.of_equiv
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).symm.toLinearEquiv
    · have hs := ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi)
      let : Subsingleton ((complex M []).X i) := hs
      exact Module.Free.of_subsingleton R _
  | append_singleton rs r ih =>
    rw [complex_append_singleton]
    let := ih (i + 1)
    let := ih i
    exact Module.Free.of_equiv (stepTermIso (complex M rs) r i).symm.toLinearEquiv

theorem term_finite (M : ModuleCat.{u} R) [Module.Finite R M] (rs : List R) (i : ℤ) :
    Module.Finite R ((complex M rs).X i) := by
  induction rs using List.reverseRecOn generalizing i with
  | nil =>
    by_cases hi : i = 0
    · subst i
      exact Module.Finite.equiv (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).symm.toLinearEquiv
    · have hs := ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi)
      let : Subsingleton ((complex M []).X i) := hs
      infer_instance
  | append_singleton rs r ih =>
    rw [complex_append_singleton]
    let := ih (i + 1)
    let := ih i
    exact Module.Finite.equiv (stepTermIso (complex M rs) r i).symm.toLinearEquiv

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.RegularSequenceKoszul
