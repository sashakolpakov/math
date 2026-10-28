import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.EventualGrid
import Mathlib.Tactic.Ring

/-! # Difference Polynomial -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.DifferencePolynomial

noncomputable section

/-! The first difference of the power monomial has degree one less and leading coefficient equal to its exponent. This calculation applies to the actual section-cokernel Euler sequence without choosing a new Euler normalization. -/
open _root_.Polynomial

def powerDifferencePolynomial (n : ℕ) : Polynomial ℚ := (X + 1) ^ n - X ^ n

theorem powerDifferencePolynomial_eval (n : ℕ) (x : ℚ) :
    (powerDifferencePolynomial n).eval x = (x + 1) ^ n - x ^ n := by
  simp [powerDifferencePolynomial]

theorem powerDifferencePolynomial_succ (n : ℕ) :
    powerDifferencePolynomial (n + 1) =
      X * powerDifferencePolynomial n + powerDifferencePolynomial n + X ^ n := by
  dsimp only [powerDifferencePolynomial]
  rw [pow_succ (X + 1), pow_succ X]
  ring

theorem powerDifferencePolynomial_degree_coeff (n : ℕ) :
    (powerDifferencePolynomial (n + 1)).natDegree = n ∧
      (powerDifferencePolynomial (n + 1)).coeff n = (n + 1 : ℚ) := by
  induction n with
  | zero => simp [powerDifferencePolynomial]
  | succ n ih =>
    have hrec := powerDifferencePolynomial_succ (n + 1)
    have hzero : (powerDifferencePolynomial (n + 1)).coeff (n + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (ih.1.trans_lt (Nat.lt_succ_self n))
    have hcoeff : (powerDifferencePolynomial ((n + 1) + 1)).coeff (n + 1) =
        ((n + 1) + 1 : ℚ) := by
      rw [hrec, coeff_add, coeff_add, coeff_X_mul, ih.2, hzero, coeff_X_pow_self]
      ring
    have hbound : (powerDifferencePolynomial ((n + 1) + 1)).natDegree ≤ n + 1 := by
      rw [hrec]
      apply natDegree_add_le_of_degree_le
      · apply natDegree_add_le_of_degree_le
        · exact natDegree_mul_le.trans (by rw [natDegree_X, ih.1]; omega)
        · rw [ih.1]
          omega
      · rw [natDegree_X_pow]
    refine ⟨natDegree_eq_of_le_of_coeff_ne_zero hbound ?_, by simpa only [Nat.cast_add, Nat.cast_one] using hcoeff⟩
    rw [hcoeff]
    positivity

theorem powerDifferencePolynomial_natDegree {n : ℕ} (hn : 0 < n) :
    (powerDifferencePolynomial n).natDegree = n - 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
    (powerDifferencePolynomial_degree_coeff m).1

theorem powerDifferencePolynomial_leadingCoeff (n : ℕ) :
    (powerDifferencePolynomial n).leadingCoeff = (n : ℚ) := by
  cases n with
  | zero => simp [powerDifferencePolynomial]
  | succ n =>
    change (powerDifferencePolynomial (n + 1)).coeff
      (powerDifferencePolynomial (n + 1)).natDegree = ((n + 1 : ℕ) : ℚ)
    rw [(powerDifferencePolynomial_degree_coeff n).1,
      (powerDifferencePolynomial_degree_coeff n).2, Nat.cast_add, Nat.cast_one]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.DifferencePolynomial
