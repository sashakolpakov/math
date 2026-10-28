import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! # Polynomial Top Coefficient -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialTopCoefficient.Construction

/-! Equal degree and leading coefficient determine every coefficient at or above that degree. -/

open _root_.Polynomial

theorem polynomial_coeff_eq_of_same_leading_data
    (P Q : Polynomial ℚ) (hdeg : P.natDegree = Q.natDegree)
    (hlc : P.leadingCoeff = Q.leadingCoeff) (d : ℕ) (hd : P.natDegree ≤ d) :
    P.coeff d = Q.coeff d := by
  by_cases h : P.natDegree = d
  · rw [← h, coeff_natDegree, hdeg, coeff_natDegree]
    exact hlc
  · have hp : P.natDegree < d := lt_of_le_of_ne hd h
    rw [coeff_eq_zero_of_natDegree_lt hp, coeff_eq_zero_of_natDegree_lt (hdeg ▸ hp)]

end OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialTopCoefficient.Construction
