import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic

/-! # Polynomial Difference -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialDifference.Construction

noncomputable section

/-! Finite differences lower polynomial degree. Integer values at all
sufficiently large integers give an integral factorial-scaled top coefficient. -/

open _root_.Polynomial

def polynomialDifference (P : Polynomial ℚ) : Polynomial ℚ := taylor 1 P - P

theorem polynomialDifference_eval (P : Polynomial ℚ) (x : ℚ) :
    (polynomialDifference P).eval x = P.eval (x + 1) - P.eval x := by
  rw [polynomialDifference, eval_sub, taylor_eval]

theorem polynomialDifference_natDegree_le (P : Polynomial ℚ) :
    (polynomialDifference P).natDegree ≤ P.natDegree - 1 := by
  by_cases hp : P = 0
  · simp [hp, polynomialDifference]
  by_cases hd : P.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hd]
    simp [polynomialDifference]
  by_cases hq : polynomialDifference P = 0
  · simp [hq]
  have hdeg : (polynomialDifference P).degree < P.degree :=
    degree_sub_lt_right (degree_taylor P 1) hp (leadingCoeff_taylor 1 P)
  have hlt : (polynomialDifference P).natDegree < P.natDegree :=
    (natDegree_lt_iff_degree_lt hq).mpr
      (hdeg.trans_eq (degree_eq_natDegree hp))
  omega

theorem polynomialDifference_coeff_top (P : Polynomial ℚ) (d : ℕ)
    (hd : P.natDegree ≤ d + 1) :
    (polynomialDifference P).coeff d = (d + 1 : ℕ) * P.coeff (d + 1) := by
  have hb : (hasseDeriv d P).natDegree ≤ 1 :=
    (natDegree_hasseDeriv_le P d).trans (by omega)
  have he := eq_X_add_C_of_natDegree_le_one hb
  rw [polynomialDifference, coeff_sub, taylor_coeff, he]
  simp only [eval_add, eval_mul, eval_C, eval_X, mul_one, hasseDeriv_coeff,
    zero_add, Nat.choose_self, Nat.cast_one, one_mul]
  rw [Nat.add_comm 1 d, Nat.choose_succ_self_right]
  ring

theorem polynomialDifference_natDegree (P : Polynomial ℚ) (hd : 0 < P.natDegree) :
    (polynomialDifference P).natDegree = P.natDegree - 1 := by
  have hs : P.natDegree - 1 + 1 = P.natDegree := Nat.sub_add_cancel hd
  have hc : (polynomialDifference P).coeff (P.natDegree - 1) ≠ 0 := by
    rw [polynomialDifference_coeff_top P _ (by omega), hs, coeff_natDegree]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hd.ne')
      (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt hd))
  exact le_antisymm (polynomialDifference_natDegree_le P) (le_natDegree_of_ne_zero hc)

theorem polynomialDifference_leadingCoeff (P : Polynomial ℚ) (hd : 0 < P.natDegree) :
    (polynomialDifference P).leadingCoeff = (P.natDegree : ℚ) * P.leadingCoeff := by
  rw [leadingCoeff, polynomialDifference_natDegree P hd,
    polynomialDifference_coeff_top P _ (by omega), Nat.sub_add_cancel hd, coeff_natDegree]

theorem polynomialDifference_factorial_leadingCoeff (P : Polynomial ℚ)
    (hd : 0 < P.natDegree) :
    ((polynomialDifference P).natDegree.factorial : ℚ) * (polynomialDifference P).leadingCoeff =
      (P.natDegree.factorial : ℚ) * P.leadingCoeff := by
  rw [polynomialDifference_natDegree P hd, polynomialDifference_leadingCoeff P hd]
  have hf := Nat.factorial_succ (P.natDegree - 1)
  rw [Nat.sub_add_cancel hd] at hf
  rw [hf, Nat.cast_mul]
  ring

theorem polynomial_factorial_coeff_integral_of_eventual_integer_values
    (P : Polynomial ℚ) (d : ℕ) (hd : P.natDegree ≤ d)
    (b : ℕ) (h : ∀ n : ℕ, b ≤ n → ∃ z : ℤ, P.eval (n : ℚ) = z) :
    ∃ z : ℤ, (d.factorial : ℚ) * P.coeff d = z := by
  induction d generalizing P with
  | zero =>
      obtain ⟨z, hz⟩ := h b le_rfl
      refine ⟨z, ?_⟩
      rw [eq_C_of_natDegree_le_zero hd, eval_C] at hz
      simpa using hz
  | succ d ih =>
      have hdiff : (polynomialDifference P).natDegree ≤ d :=
        (polynomialDifference_natDegree_le P).trans (by omega)
      have hint : ∀ n : ℕ, b ≤ n →
          ∃ z : ℤ, (polynomialDifference P).eval (n : ℚ) = z := by
        intro n hn
        obtain ⟨a, ha⟩ := h (n + 1) (by omega)
        obtain ⟨c, hc⟩ := h n hn
        refine ⟨a - c, ?_⟩
        rw [polynomialDifference_eval, ← Nat.cast_add_one, ha, hc, Int.cast_sub]
      obtain ⟨z, hz⟩ := ih (polynomialDifference P) hdiff hint
      refine ⟨z, ?_⟩
      rw [polynomialDifference_coeff_top P d hd] at hz
      rw [Nat.factorial_succ, Nat.cast_mul]
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hz

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialDifference.Construction
