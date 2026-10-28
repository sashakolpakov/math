import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Ring.Commute
import Lean.Elab.Tactic.Omega

/-! # Permutation Last -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.PermutationLast.Cycles

/-!
# Permutations classified by their last value

Inserting a final value into an ordered permutation of the remaining values is
an actual equivalence of finite permutation types. The sign identity gives the
alternating coefficient needed for the outer faces of barycentric subdivision.
-/

open Equiv

/-- Insert the value `i` at the last position, retaining the increasing order
identification of its complement. -/
def insertLastPermutation {n : ℕ} (i : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (Fin (n + 2)) :=
  Fin.cycleIcc i (Fin.last (n + 1)) *
    τ.extendDomain (finSuccAboveEquiv (Fin.last (n + 1)))

/-- The inserted permutation sends its last position to the chosen value. -/
@[simp] theorem insertLastPermutation_apply_last {n : ℕ} (i : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) :
    insertLastPermutation i τ (Fin.last (n + 1)) = i := by
  rw [insertLastPermutation, Equiv.Perm.mul_apply,
    Equiv.Perm.extendDomain_apply_not_subtype _ _ (by simp)]
  exact Fin.cycleIcc_of_last (Fin.le_last i)

/-- The other positions follow the canonical order-preserving deletion of `i`. -/
@[simp] theorem insertLastPermutation_apply_castSucc {n : ℕ} (i : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    insertLastPermutation i τ k.castSucc = i.succAbove (τ k) := by
  have hext : τ.extendDomain (finSuccAboveEquiv (Fin.last (n + 1))) k.castSucc =
      (τ k).castSucc := by
    simpa only [finSuccAboveEquiv_apply, Fin.succAbove_last] using
      τ.extendDomain_apply_image (finSuccAboveEquiv (Fin.last (n + 1))) k
  rw [insertLastPermutation, Equiv.Perm.mul_apply, hext]
  simpa only [Function.comp_apply, Fin.succAbove_last] using
    congrFun (Fin.cycleIcc_comp_succAbove i (Fin.last (n + 1)) (Fin.le_last i)) (τ k)

/-- The insertion parameters can be recovered uniquely. -/
theorem insertLastPermutation_injective (n : ℕ) :
    Function.Injective (fun p : Fin (n + 2) × Equiv.Perm (Fin (n + 1)) =>
      insertLastPermutation p.1 p.2) := by
  rintro ⟨i, τ⟩ ⟨j, υ⟩ h
  have hij : i = j := by
    simpa only [insertLastPermutation_apply_last] using
      congrArg (fun σ => σ (Fin.last (n + 1))) h
  subst j
  have hτυ : τ = υ := by
    apply Equiv.ext
    intro k
    apply Fin.succAbove_right_injective (p := i)
    simpa only [insertLastPermutation_apply_castSucc] using
      congrArg (fun σ => σ k.castSucc) h
  exact congrArg (Prod.mk i) hτυ

/-- Every permutation is obtained uniquely by inserting its last value. -/
noncomputable def insertLastPermutationEquiv (n : ℕ) :
    (Fin (n + 2) × Equiv.Perm (Fin (n + 1))) ≃ Equiv.Perm (Fin (n + 2)) :=
  Equiv.ofBijective (fun p => insertLastPermutation p.1 p.2)
    ⟨insertLastPermutation_injective n,
      (Finite.injective_iff_surjective_of_equiv
        (Equiv.Perm.decomposeFin (n := n + 1)).symm).mp
          (insertLastPermutation_injective n)⟩

@[simp] theorem insertLastPermutationEquiv_apply (n : ℕ)
    (p : Fin (n + 2) × Equiv.Perm (Fin (n + 1))) :
    insertLastPermutationEquiv n p = insertLastPermutation p.1 p.2 := rfl

/-- The first coordinate of the inverse equivalence is the last image itself. -/
@[simp] theorem insertLastPermutationEquiv_symm_fst {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) :
    ((insertLastPermutationEquiv n).symm σ).1 = σ (Fin.last (n + 1)) := by
  have h := congrArg (fun τ => τ (Fin.last (n + 1)))
    ((insertLastPermutationEquiv n).apply_symm_apply σ)
  simpa only [insertLastPermutationEquiv_apply, insertLastPermutation_apply_last] using h

/-- Inserting `i` contributes precisely the sign of the cycle from `i` to the last value. -/
theorem sign_insertLastPermutation_factor {n : ℕ} (i : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) :
    (Equiv.Perm.sign (insertLastPermutation i τ) : ℤ) =
      (-1 : ℤ) ^ (n + 1 - i.val) * (Equiv.Perm.sign τ : ℤ) := by
  rw [insertLastPermutation, Equiv.Perm.sign_mul, Equiv.Perm.sign_extendDomain,
    Fin.sign_cycleIcc_of_le (Fin.le_last i)]
  simp

/-- The outer-face coefficient agrees with the deleted vertex's alternating sign. -/
theorem sign_insertLastPermutation {n : ℕ} (i : Fin (n + 2))
    (τ : Equiv.Perm (Fin (n + 1))) :
    (Equiv.Perm.sign (insertLastPermutation i τ) : ℤ) * (-1 : ℤ) ^ (n + 1) =
      (-1 : ℤ) ^ i.val * (Equiv.Perm.sign τ : ℤ) := by
  have hp : (-1 : ℤ) ^ (n + 1 - i.val) * (-1 : ℤ) ^ (n + 1) = (-1 : ℤ) ^ i.val := by
    rw [← pow_add, neg_one_pow_eq_pow_mod_two ((n + 1 - i.val) + (n + 1)),
      neg_one_pow_eq_pow_mod_two i.val]
    congr 1
    have hi := i.isLt
    omega
  rw [sign_insertLastPermutation_factor, mul_right_comm, hp]

end OAI.AlgebraicGeometry.CycleClass.Geometric.PermutationLast.Cycles
