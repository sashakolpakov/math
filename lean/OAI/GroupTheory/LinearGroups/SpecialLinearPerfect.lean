import Mathlib.GroupTheory.IsPerfect
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Tactic
import Lean.Util.CollectAxioms

/-! # Special Linear Perfect -/

namespace OAI.GroupTheory.LinearGroups.SpecialLinearPerfect.SLConstruction

/-!
# SL3Perfect: perfectness of SL₃ over a field

This file proves the statements of `Statements/SL3Perfect.lean` independently of its
placeholders. The proof is algebraic and applies to every field, hence to the
nonarchimedean local fields in the application.
-/

universe u v

open _root_.Matrix _root_.Matrix.SpecialLinearGroup
open scoped commutatorElement

variable {k : Type u} [Field k]

/-- The third index realizes every elementary transvection as a commutator. -/
lemma transvection_commutator
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {i j l : ι} (hij : i ≠ j) (hil : i ≠ l) (hlj : l ≠ j) (a : k) :
    ⁅transvection hil a, transvection hlj (1 : k)⁆ = transvection hij a := by
  rw [commutatorElement_def, transvection_inv, transvection_inv]
  apply Subtype.ext
  simp [transvection_coe, mul_add, add_mul,
    single_mul_single_of_ne _ _ _ _ hil.symm,
    single_mul_single_of_ne _ _ _ _ hlj.symm,
    single_mul_single_of_ne _ _ _ _ hij.symm, ← single_neg]
  abel

/-- A determinant-one diagonal block is a product of six transvections. -/
lemma diag2n_transvection_decomposition
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {i j : ι} (hij : i ≠ j) (a : k) (ha : a ≠ 0) :
    diag2n hij a ha =
      transvection hij a * transvection hij.symm (-a⁻¹) *
      transvection hij a * transvection hij (-1) *
      transvection hij.symm 1 * transvection hij (-1) := by
  apply Subtype.ext
  simp only [coe_mul, transvection_coe, diag2n_coe]
  simp only [mul_add, add_mul, one_mul, mul_one,
    single_mul_single_same,
    single_mul_single_of_ne _ _ _ _ hij,
    single_mul_single_of_ne _ _ _ _ hij.symm,
    add_zero]
  ext r s
  by_cases hri : r = i <;> by_cases hrj : r = j <;>
    by_cases hsi : s = i <;> by_cases hsj : s = j <;>
    simp_all [Matrix.single, Matrix.diagonal_apply, Matrix.one_apply, eq_comm]

/-- Every elementary generator of SL₃ belongs to its commutator subgroup. -/
lemma sl3_transvection_mem_commutator
    {i j : Fin 3} (hij : i ≠ j) (a : k) :
    transvection hij a ∈ commutator (Matrix.SpecialLinearGroup (Fin 3) k) := by
  obtain ⟨l, hli, hlj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide)
  rw [← transvection_commutator hij hli.symm hlj a]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- SL₃ over any field is perfect as an abstract group. -/
theorem sl3_isPerfect (k : Type u) [Field k] :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) k) := by
  refine ⟨le_antisymm le_top ?_⟩
  intro g _
  refine diagonal_transvection_induction'
    (fun x => x ∈ commutator (Matrix.SpecialLinearGroup (Fin 3) k)) g ?_ ?_ ?_
  · intro i j hij a ha
    rw [diag2n_transvection_decomposition hij a ha]
    repeat' apply Subgroup.mul_mem
    all_goals exact sl3_transvection_mem_commutator _ _
  · intro i j hij a
    exact sl3_transvection_mem_commutator hij a
  · intro A B hA hB
    exact Subgroup.mul_mem _ hA hB

/-- Every homomorphism from SL₃ to an abelian group is trivial. -/
theorem sl3_hom_to_abelian_eq_one
    (k : Type u) [Field k]
    (A : Type v) [CommGroup A]
    (χ : Matrix.SpecialLinearGroup (Fin 3) k →* A) :
    χ = 1 := by
  ext g
  change χ g = 1
  apply MonoidHom.mem_ker.mp
  apply Abelianization.commutator_subset_ker χ
  rw [(sl3_isPerfect k).commutator_eq_top]
  exact Subgroup.mem_top _

end OAI.GroupTheory.LinearGroups.SpecialLinearPerfect.SLConstruction
