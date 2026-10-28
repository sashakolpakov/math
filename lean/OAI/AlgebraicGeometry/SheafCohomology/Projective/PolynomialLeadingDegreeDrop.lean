import Mathlib.Algebra.Polynomial.Degree.Operations

/-! # Polynomial Leading Degree Drop -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialLeadingDegreeDrop

/-! Cancellation of equal leading data lowers a polynomial degree bound by one. -/

open _root_.Polynomial

theorem polynomial_sub_degree_lt_of_same_leading_data (P Q : Polynomial ℚ)
    (hdeg : Q.natDegree = P.natDegree) (hlc : Q.leadingCoeff = P.leadingCoeff)
    (d : ℕ) (hP : P.degree < ((d + 1 : ℕ) : WithBot ℕ)) :
    (Q - P).degree < (d : WithBot ℕ) := by
  by_cases hp : P = 0
  · have hq : Q = 0 := leadingCoeff_eq_zero.mp (by simpa only [hp, leadingCoeff_zero] using hlc)
    rw [hp, hq, sub_self, degree_zero]
    exact WithBot.bot_lt_coe d
  · have hq : Q ≠ 0 := leadingCoeff_ne_zero.mp (hlc ▸ leadingCoeff_ne_zero.mpr hp)
    have he : Q.degree = P.degree := by rw [degree_eq_natDegree hq, degree_eq_natDegree hp, hdeg]
    have hd := degree_sub_lt_right he hp hlc
    have hn : P.natDegree < d + 1 := by
      rw [degree_eq_natDegree hp] at hP
      exact WithBot.coe_lt_coe.mp hP
    apply hd.trans_le
    rw [degree_eq_natDegree hp]
    exact WithBot.coe_le_coe.mpr (Nat.le_of_lt_succ hn)

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialLeadingDegreeDrop
