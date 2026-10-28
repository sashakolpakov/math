/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.DeletedTupleSigns

/-! # Permuted Tuple Signs -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.PermutedTupleSigns

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

/-- The permutation induced on a tuple after deleting `r` and applying `σ`. -/
def cechPermDeleteFull {n : ℕ} (σ : Equiv.Perm (Fin (n + 2)))
    (r : Fin (n + 2)) : Equiv.Perm (Fin (n + 2)) :=
  (r.cycleRange.symm.trans σ).trans (σ r).cycleRange

/-- The restriction of `cechPermDeleteFull` to the positive indices. -/
def cechPermDelete {n : ℕ} (σ : Equiv.Perm (Fin (n + 2)))
    (r : Fin (n + 2)) : Equiv.Perm (Fin (n + 1)) :=
  (Equiv.Perm.decomposeFin (cechPermDeleteFull σ r)).2

theorem cechPermDeleteFull_apply_zero {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2)) :
    cechPermDeleteFull σ r 0 = 0 := by
  simp [cechPermDeleteFull]

theorem cechPermDeleteFull_eq_decomposeFin {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2)) :
    cechPermDeleteFull σ r =
      Equiv.Perm.decomposeFin.symm (0, cechPermDelete σ r) := by
  apply Equiv.Perm.decomposeFin.injective
  apply Prod.ext
  · simpa [Equiv.Perm.decomposeFin] using
      cechPermDeleteFull_apply_zero σ r
  · rfl

theorem cechPermDeleteFull_apply_succ {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2))
    (x : Fin (n + 1)) :
    cechPermDeleteFull σ r x.succ = (cechPermDelete σ r x).succ := by
  rw [cechPermDeleteFull_eq_decomposeFin]
  simp

theorem succAbove_cechPermDelete {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2))
    (x : Fin (n + 1)) :
    (σ r).succAbove (cechPermDelete σ r x) = σ (r.succAbove x) := by
  apply (σ r).cycleRange.injective
  rw [Fin.cycleRange_succAbove]
  rw [← cechPermDeleteFull_apply_succ σ r x]
  simp [cechPermDeleteFull]

theorem cechPermDelete_sign {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2)) :
    (Equiv.Perm.sign (cechPermDelete σ r) : ℤ) =
      (-1 : ℤ) ^ (r : ℕ) * (Equiv.Perm.sign σ : ℤ) *
        (-1 : ℤ) ^ (σ r : ℕ) := by
  have hsign := congrArg Equiv.Perm.sign
    (cechPermDeleteFull_eq_decomposeFin σ r)
  simp only [Equiv.Perm.decomposeFin.symm_sign, ite_eq_left, one_mul] at hsign
  rw [← hsign]
  simp [cechPermDeleteFull, Equiv.Perm.sign_trans, Units.val_mul,
    mul_comm, mul_left_comm]

theorem cechPermDelete_signed_coefficient {n : ℕ}
    (σ : Equiv.Perm (Fin (n + 2))) (r : Fin (n + 2)) :
    (-1 : ℤ) ^ (r : ℕ) * (Equiv.Perm.sign (cechPermDelete σ r) : ℤ) =
      (Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ (σ r : ℕ) := by
  rw [cechPermDelete_sign]
  have hr : (-1 : ℤ) ^ (r : ℕ) * (-1 : ℤ) ^ (r : ℕ) = 1 := by
    rw [← pow_add, (Even.add_self (r : ℕ)).neg_one_pow]
  rw [← mul_assoc ((-1 : ℤ) ^ (r : ℕ))
      (((-1 : ℤ) ^ (r : ℕ)) * (Equiv.Perm.sign σ : ℤ))
      ((-1 : ℤ) ^ (σ r : ℕ)),
    ← mul_assoc ((-1 : ℤ) ^ (r : ℕ))
      ((-1 : ℤ) ^ (r : ℕ)) (Equiv.Perm.sign σ : ℤ),
    hr, one_mul]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.PermutedTupleSigns
