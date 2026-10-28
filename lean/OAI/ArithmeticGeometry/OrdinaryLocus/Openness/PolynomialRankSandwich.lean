import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PolynomialGrowthDegree

/-! # Polynomial Rank Sandwich -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PolynomialRankSandwich.Construction

/-! The numerical degree follows from a bounded shift comparison of section spaces. -/

open _root_.Polynomial

theorem polynomial_leadingCoeff_eq_of_shift_bounds
    (P Q : Polynomial ℚ) (D : ℚ) (hd : Q.natDegree = P.natDegree)
    (b c : ℕ)
    (hlo : ∀ n : ℕ, b ≤ n → D * P.eval (n : ℚ) ≤ Q.eval ((n : ℚ) + c))
    (hhi : ∀ n : ℕ, b ≤ n → Q.eval (n : ℚ) ≤ D * P.eval ((n : ℚ) + c)) :
    Q.leadingCoeff = D * P.leadingCoeff := by
  let T : Polynomial ℚ := Polynomial.X + Polynomial.C (c : ℚ)
  have hT : T.natDegree = 1 := Polynomial.natDegree_X_add_C (c : ℚ)
  have hPT : (P.comp T).natDegree = P.natDegree := by
    rw [Polynomial.natDegree_comp, hT, mul_one]
  have hQT : (Q.comp T).natDegree = P.natDegree := by
    rw [Polynomial.natDegree_comp, hT, mul_one, hd]
  have hl := PolynomialGrowthDegree.Construction.polynomial_coeff_le_of_eventually_nat_eval_le
    (Polynomial.C D * P) (Q.comp T) P.natDegree
    (Polynomial.natDegree_C_mul_le D P) hQT.le b (fun n hn => by
      simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
        T, Polynomial.eval_add, Polynomial.eval_X] using hlo n hn)
  have hh := PolynomialGrowthDegree.Construction.polynomial_coeff_le_of_eventually_nat_eval_le
    Q (Polynomial.C D * P.comp T) P.natDegree hd.le
    ((Polynomial.natDegree_C_mul_le D (P.comp T)).trans hPT.le) b (fun n hn => by
      simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_comp,
        T, Polynomial.eval_add, Polynomial.eval_X] using hhi n hn)
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_natDegree, ← hQT,
    Polynomial.coeff_natDegree, PolynomialGrowthDegree.Construction.polynomial_leadingCoeff_comp_add] at hl
  rw [← hd, Polynomial.coeff_natDegree] at hh
  rw [Polynomial.coeff_C_mul, hd, ← hPT, Polynomial.coeff_natDegree,
    PolynomialGrowthDegree.Construction.polynomial_leadingCoeff_comp_add] at hh
  exact le_antisymm hh hl

theorem polynomial_rank_eq_power_of_rescaling_and_shift_bounds
    (P Q : Polynomial ℚ) (hP : P ≠ 0) (D a : ℕ) (ha : 0 < a)
    (he : Q = P.comp (Polynomial.X * Polynomial.C (a : ℚ)))
    (b c : ℕ)
    (hlo : ∀ n : ℕ, b ≤ n → (D : ℚ) * P.eval (n : ℚ) ≤ Q.eval ((n : ℚ) + c))
    (hhi : ∀ n : ℕ, b ≤ n → Q.eval (n : ℚ) ≤ (D : ℚ) * P.eval ((n : ℚ) + c)) :
    D = a ^ P.natDegree := by
  have ha' : (a : ℚ) ≠ 0 := by exact_mod_cast ha.ne'
  have hd : Q.natDegree = P.natDegree := by
    rw [he, Polynomial.natDegree_comp, Polynomial.natDegree_mul_C ha',
      Polynomial.natDegree_X, mul_one]
  have hl := polynomial_leadingCoeff_eq_of_shift_bounds P Q D hd b c hlo hhi
  rw [he, PolynomialGrowthDegree.Construction.polynomial_leadingCoeff_comp_mul P a ha'] at hl
  have hc : (D : ℚ) = (a : ℚ) ^ P.natDegree := by
    apply mul_right_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hP)
    exact hl.symm.trans (mul_comm _ _)
  exact_mod_cast hc

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PolynomialRankSandwich.Construction
