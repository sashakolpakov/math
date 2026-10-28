import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialPositivity
import Mathlib.Algebra.Polynomial.Taylor

/-! # Polynomial Comparison -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialComparison.Construction

noncomputable section

/-! Eventual inequalities of section counts compare polynomial degrees.
Mutual bounds after fixed shifts force equality of degrees and leading coefficients. -/

open _root_.Polynomial

theorem polynomial_natDegree_le_of_eventual_nat_eval_le
    (P Q : Polynomial ℚ) (hP : 0 < P.leadingCoeff)
    (b : ℕ) (h : ∀ n : ℕ, b ≤ n → P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    P.natDegree ≤ Q.natDegree := by
  by_contra hd
  have hdeg : Q.degree < P.degree := degree_lt_degree (lt_of_not_ge hd)
  have hc := PolynomialPositivity.Construction.polynomial_leadingCoeff_nonneg_of_eventual_nat_nonneg (Q - P) b
    (fun n hn => by simpa only [eval_sub, sub_nonneg] using h n hn)
  rw [leadingCoeff_sub_of_degree_lt' hdeg] at hc
  exact (neg_neg_of_pos hP).not_ge hc

theorem polynomial_coeff_le_of_eventual_nat_eval_le
    (P Q : Polynomial ℚ) (d : ℕ) (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d)
    (b : ℕ) (h : ∀ n : ℕ, b ≤ n → P.eval (n : ℚ) ≤ Q.eval (n : ℚ)) :
    P.coeff d ≤ Q.coeff d := by
  let S := Q - P
  have hd : S.natDegree ≤ d := (natDegree_sub_le Q P).trans (max_le hQ hP)
  have hc : 0 ≤ S.coeff d := by
    rcases lt_or_eq_of_le hd with hd | hd
    · rw [coeff_eq_zero_of_natDegree_lt hd]
    · rw [← hd, coeff_natDegree]
      exact PolynomialPositivity.Construction.polynomial_leadingCoeff_nonneg_of_eventual_nat_nonneg S b
        (fun n hn => by simpa only [S, eval_sub, sub_nonneg] using h n hn)
  simpa only [S, coeff_sub, sub_nonneg] using hc

theorem polynomial_degree_leadingCoeff_eq_of_mutual_shift_bounds
    (P Q : Polynomial ℚ) (hP : 0 < P.leadingCoeff) (hQ : 0 < Q.leadingCoeff)
    (b c : ℕ)
    (hPQ : ∀ n : ℕ, b ≤ n → P.eval (n : ℚ) ≤ Q.eval ((n : ℚ) + c))
    (hQP : ∀ n : ℕ, b ≤ n → Q.eval (n : ℚ) ≤ P.eval ((n : ℚ) + c)) :
    P.natDegree = Q.natDegree ∧ P.leadingCoeff = Q.leadingCoeff := by
  have hdPQ : P.natDegree ≤ Q.natDegree := by
    simpa only [natDegree_taylor] using
      polynomial_natDegree_le_of_eventual_nat_eval_le P (taylor (c : ℚ) Q) hP b
        (fun n hn => by simpa only [taylor_eval] using hPQ n hn)
  have hdQP : Q.natDegree ≤ P.natDegree := by
    simpa only [natDegree_taylor] using
      polynomial_natDegree_le_of_eventual_nat_eval_le Q (taylor (c : ℚ) P) hQ b
        (fun n hn => by simpa only [taylor_eval] using hQP n hn)
  have hd := le_antisymm hdPQ hdQP
  refine ⟨hd, le_antisymm ?_ ?_⟩
  · have hc := polynomial_coeff_le_of_eventual_nat_eval_le P (taylor (c : ℚ) Q)
      Q.natDegree hdPQ (by rw [natDegree_taylor]) b
      (fun n hn => by simpa only [taylor_eval] using hPQ n hn)
    rw [← hd, coeff_natDegree] at hc
    simpa only [hd, coeff_taylor_natDegree] using hc
  · have hc := polynomial_coeff_le_of_eventual_nat_eval_le Q (taylor (c : ℚ) P)
      P.natDegree hdQP (by rw [natDegree_taylor]) b
      (fun n hn => by simpa only [taylor_eval] using hQP n hn)
    rw [hd, coeff_natDegree] at hc
    simpa only [← hd, coeff_taylor_natDegree] using hc

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialComparison.Construction
