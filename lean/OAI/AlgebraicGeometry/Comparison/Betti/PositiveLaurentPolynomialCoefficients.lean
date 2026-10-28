import OAI.AlgebraicGeometry.SheafCohomology.Projective.NonnegativeLaurentPolynomials

/-! # Positive Laurent Polynomial Coefficients -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PositiveLaurentPolynomialCoefficients.Dolbeault

noncomputable section

/-! The original nonnegative Laurent coefficient coordinates preserve polynomial monomials. -/

open _root_.MvPolynomial

local instance (N k : ℕ) : DecidableEq (SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin N) (k : ℤ)) := Classical.decEq _

theorem homogeneousPolynomialCoefficientsEquiv_apply (N k : ℕ)
    (P : homogeneousSubmodule (Fin N) ℂ k) (e : SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin N) (k : ℤ)) :
    SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial.homogeneousPolynomialCoefficientsEquiv ℂ k P e =
      AddMonoidAlgebra.coeff (P.val) ((SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial.nonnegativeLaurentWeightEquivDegree k e).val) := rfl

def positiveLaurentPolynomialMonomial (N k : ℕ) (e : SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin N) (k : ℤ)) (c : ℂ) :
    homogeneousSubmodule (Fin N) ℂ k :=
  ⟨MvPolynomial.monomial (SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial.nonnegativeLaurentWeightEquivDegree k e).val c,
    MvPolynomial.isHomogeneous_monomial c (SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial.nonnegativeLaurentWeightEquivDegree k e).property⟩

theorem positiveLaurentPolynomialMonomial_coefficients (N k : ℕ)
    (e : SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight (Fin N) (k : ℤ)) (c : ℂ) :
    SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial.homogeneousPolynomialCoefficientsEquiv ℂ k (positiveLaurentPolynomialMonomial N k e c) =
      Pi.single e c := by
  funext f
  rw [homogeneousPolynomialCoefficientsEquiv_apply]
  change AddMonoidAlgebra.coeff ((MvPolynomial.monomial (SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial.nonnegativeLaurentWeightEquivDegree k e).val c)) ((SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial.nonnegativeLaurentWeightEquivDegree k f).val) = _
  by_cases h : e = f
  · subst f
    simp
  · have he : (SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial.nonnegativeLaurentWeightEquivDegree k e).val ≠
        (SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial.nonnegativeLaurentWeightEquivDegree k f).val := by
      intro he
      exact h ((SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial.nonnegativeLaurentWeightEquivDegree k).injective (Subtype.ext he))
    simp [MvPolynomial.coeff_monomial, he, Pi.single_eq_of_ne (Ne.symm h)]

end

end OAI.AlgebraicGeometry.Comparison.Betti.PositiveLaurentPolynomialCoefficients.Dolbeault
