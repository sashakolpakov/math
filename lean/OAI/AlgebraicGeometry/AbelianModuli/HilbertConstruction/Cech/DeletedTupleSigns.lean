/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.ProjectionSplitting
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.GroupTheory.Perm.Fin

/-! # Deleted Tuple Signs -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.DeletedTupleSigns

noncomputable section

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Category _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite _root_.TopologicalSpace
universe u

/-- The permutation relating the two faces obtained by deleting `k` and `l`. -/
def cechDeleteSwapFullPerm {n : ℕ} (k l : Fin (n + 2)) :
    Equiv.Perm (Fin (n + 2)) :=
  (k.cycleRange.symm.trans (Equiv.swap k l)).trans l.cycleRange

/-- The restriction of `cechDeleteSwapFullPerm` to the positive indices. -/
def cechDeleteSwapPerm {n : ℕ} (k l : Fin (n + 2)) :
    Equiv.Perm (Fin (n + 1)) :=
  (Equiv.Perm.decomposeFin (cechDeleteSwapFullPerm k l)).2

theorem cechDeleteSwapFullPerm_apply_zero {n : ℕ} (k l : Fin (n + 2)) :
    cechDeleteSwapFullPerm k l 0 = 0 := by
  simp [cechDeleteSwapFullPerm]

theorem cechDeleteSwapFullPerm_eq_decomposeFin {n : ℕ}
    (k l : Fin (n + 2)) :
    cechDeleteSwapFullPerm k l =
      Equiv.Perm.decomposeFin.symm (0, cechDeleteSwapPerm k l) := by
  apply Equiv.Perm.decomposeFin.injective
  apply Prod.ext
  · simpa [Equiv.Perm.decomposeFin] using
      cechDeleteSwapFullPerm_apply_zero k l
  · rfl

theorem cechDeleteSwapFullPerm_apply_succ {n : ℕ}
    (k l : Fin (n + 2)) (x : Fin (n + 1)) :
    cechDeleteSwapFullPerm k l x.succ = (cechDeleteSwapPerm k l x).succ := by
  rw [cechDeleteSwapFullPerm_eq_decomposeFin]
  simp

theorem succAbove_cechDeleteSwapPerm {n : ℕ}
    (k l : Fin (n + 2)) (x : Fin (n + 1)) :
    l.succAbove (cechDeleteSwapPerm k l x) =
      Equiv.swap k l (k.succAbove x) := by
  apply l.cycleRange.injective
  rw [Fin.cycleRange_succAbove]
  rw [← cechDeleteSwapFullPerm_apply_succ k l x]
  simp [cechDeleteSwapFullPerm]

theorem comp_succAbove_cechDeleteSwapPerm_of_eq {n : ℕ}
    {ι : Type*} (i : Fin (n + 2) → ι) (k l : Fin (n + 2))
    (hkl : i k = i l) :
    (i ∘ l.succAbove) ∘ cechDeleteSwapPerm k l =
      i ∘ k.succAbove := by
  funext x
  rw [Function.comp_apply, Function.comp_apply, Function.comp_apply,
    succAbove_cechDeleteSwapPerm]
  exact Equiv.apply_swap_eq_self hkl _

theorem cechDeleteSwapPerm_sign {n : ℕ}
    (k l : Fin (n + 2)) (hkl : k ≠ l) :
    (Equiv.Perm.sign (cechDeleteSwapPerm k l) : ℤ) =
      -((-1 : ℤ) ^ (k : ℕ) * (-1 : ℤ) ^ (l : ℕ)) := by
  have hsign := congrArg Equiv.Perm.sign
    (cechDeleteSwapFullPerm_eq_decomposeFin k l)
  simp only [Equiv.Perm.decomposeFin.symm_sign, ite_eq_left, one_mul] at hsign
  rw [← hsign]
  simp [cechDeleteSwapFullPerm, Equiv.Perm.sign_trans,
    Equiv.Perm.sign_swap hkl, Units.val_mul, mul_comm]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.DeletedTupleSigns
