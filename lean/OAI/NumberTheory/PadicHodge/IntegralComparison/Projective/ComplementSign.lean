import Mathlib.GroupTheory.Perm.Fin

/-! # Complement Sign -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ComplementSign

/-! The sign of the induced ordering on complementary projective coordinates. -/

open Equiv

variable {n : ℕ}

def complement (e : Perm (Fin (n + 1))) (i : Fin (n + 1)) : Perm (Fin n) :=
  (finSuccAboveEquiv i).trans
    ((e.subtypeEquiv (fun j => by simp)).trans (finSuccAboveEquiv (e i)).symm)

@[simp] theorem succAbove_complement (e : Perm (Fin (n + 1))) (i : Fin (n + 1))
    (j : Fin n) : (e i).succAbove (complement e i j) = e (i.succAbove j) := by
  exact congrArg Subtype.val ((finSuccAboveEquiv (e i)).apply_symm_apply
    ((e.subtypeEquiv (fun j => by simp)) ((finSuccAboveEquiv i) j)))

theorem extended_complement (e : Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    Perm.decomposeFin.symm (0, complement e i) =
      (e i).cycleRange * e * i.cycleRange⁻¹ := by
  ext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp
  · simp only [Perm.decomposeFin_symm_apply_succ, swap_self, refl_apply,
      Perm.mul_apply, Equiv.Perm.inv_def, Fin.cycleRange_symm_succ]
    rw [← succAbove_complement, Fin.cycleRange_succAbove]

theorem sign_complement (e : Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    Perm.sign (complement e i) = (-1) ^ (e i).val * Perm.sign e * (-1) ^ i.val := by
  have h := congrArg Perm.sign (extended_complement e i)
  simpa only [Perm.decomposeFin.symm_sign, ite_true, one_mul, map_mul,
    Perm.sign_inv, Fin.sign_cycleRange] using h

theorem sign_complement_swap (i k : Fin (n + 1)) (h : i ≠ k) :
    Perm.sign (complement (swap i k) i) = (-1) ^ k.val * (-1) * (-1) ^ i.val := by
  rw [sign_complement, swap_apply_left, Perm.sign_swap h]

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ComplementSign
