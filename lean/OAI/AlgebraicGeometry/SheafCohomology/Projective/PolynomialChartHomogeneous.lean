import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartMap
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HomogeneousPolynomialCoefficientFormula

/-! # Polynomial Chart Homogeneous -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartHomogeneous.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-! The dehomogenized image of a homogeneous polynomial in explicit Laurent monomial coordinates. -/

universe u
variable {σ : Type} [Fintype σ] (R : Type u) [CommRing R] {m : ℕ}

theorem polynomialChartRingHom_homogeneous (a : Fin (m + 1) → σ) (n : ℕ)
    (p : homogeneousSubmodule σ R n) :
    PolynomialChartMap.MvPolynomial.polynomialChartRingHom R a p.val =
      ∑ e : LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (n : ℤ),
        AddMonoidAlgebra.single
          ((LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a (n : ℤ)).symm (PolynomialChartMap.MvPolynomial.nonnegativeLaurentWeightAllowed a n e))
          (NonnegativeLaurentPolynomials.MvPolynomial.homogeneousPolynomialCoefficientsEquiv R n p e) := by
  have hp := congrArg (fun q : homogeneousSubmodule σ R n =>
    PolynomialChartMap.MvPolynomial.polynomialChartRingHom R a q.val) (HomogeneousPolynomialCoefficientFormula.MvPolynomial.homogeneousPolynomial_eq_sum_monomials R n p)
  rw [Submodule.coe_sum, map_sum] at hp
  rw [hp]
  apply Finset.sum_congr rfl
  intro e _
  change PolynomialChartMap.MvPolynomial.polynomialChartRingHom R a
    (monomial ((NonnegativeLaurentPolynomials.MvPolynomial.nonnegativeLaurentWeightEquivDegree n) e).val
      (NonnegativeLaurentPolynomials.MvPolynomial.homogeneousPolynomialCoefficientsEquiv R n p e)) = _
  rw [PolynomialChartMap.MvPolynomial.polynomialChartRingHom_monomial, PolynomialChartMap.MvPolynomial.polynomialChartExponent_eq_homogeneous_symm]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartHomogeneous.MvPolynomial
