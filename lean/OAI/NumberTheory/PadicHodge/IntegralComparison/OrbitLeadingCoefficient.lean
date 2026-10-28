import OAI.AlgebraicGeometry.SheafCohomology.Projective.EndomorphismOrbitPolynomial

/-! # Orbit Leading Coefficient -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.OrbitLeadingCoefficient.ProjectiveCohomologyProjective

noncomputable section

/-! The highest coefficient in the Newton polynomial of an actual
additive orbit is its highest difference divided by the factorial. -/

open _root_.Polynomial

theorem endomorphismOrbitPolynomial_coeff_top
    {G : Type*} [AddCommGroup G] (T : AddMonoid.End G)
    (φ : G →+ ℤ) (x : G) (d : ℕ) :
    (AlgebraicGeometry.SheafCohomology.Projective.EndomorphismOrbitPolynomial.endomorphismOrbitPolynomial T φ x (d + 1)).coeff d =
      (φ (((T - 1) ^ d) x) : ℚ) / (d.factorial : ℚ) := by
  classical
  rw [AlgebraicGeometry.SheafCohomology.Projective.EndomorphismOrbitPolynomial.endomorphismOrbitPolynomial, finsetSum_coeff, Finset.sum_eq_single d]
  · rw [coeff_C_mul]
    have hd : (descPochhammer ℚ d).coeff d = 1 := by
      simpa only [← coeff_natDegree, descPochhammer_natDegree] using
        (monic_descPochhammer (R := ℚ) d).leadingCoeff
    rw [hd, mul_one]
  · intro k hk hkd
    rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt, mul_zero]
    rw [descPochhammer_natDegree]
    have hk' := Finset.mem_range.mp hk
    omega
  · simp

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.OrbitLeadingCoefficient.ProjectiveCohomologyProjective
