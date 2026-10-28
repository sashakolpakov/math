import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialSectionProductCriterion

/-! # Polynomial Section Product Degree -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialSectionProductDegree.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-! The section product criterion with an explicitly identified target degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem coordinateTwistPolynomial_eq_mul_of_coefficient_of_degree
    (i j : σ) (m n k : ℕ) (hdegree : m + n = k)
    (x : Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m, ⊤))
    (y : Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n, ⊤))
    (z : Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j k, ⊤))
    (h : PolynomialSectionProductCriterion.MvPolynomial.coordinateTwistChartCoefficient i j k z =
      PolynomialSectionProductCriterion.MvPolynomial.coordinateTwistChartCoefficient i j m x * PolynomialSectionProductCriterion.MvPolynomial.coordinateTwistChartCoefficient i j n y) :
    (DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j k z).val =
      (DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j m x).val *
        (DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j n y).val := by
  subst k
  exact PolynomialSectionProductCriterion.MvPolynomial.coordinateTwistPolynomial_eq_mul_of_coefficient i j m n x y z h

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialSectionProductDegree.MvPolynomial
