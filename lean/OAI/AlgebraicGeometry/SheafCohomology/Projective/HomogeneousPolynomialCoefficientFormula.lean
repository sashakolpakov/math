import OAI.AlgebraicGeometry.SheafCohomology.Projective.NonnegativeLaurentPolynomials

/-! # Homogeneous Polynomial Coefficient Formula -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.HomogeneousPolynomialCoefficientFormula.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-! Explicit monomial reconstruction in the homogeneous polynomial coefficient equivalence. -/

universe u
variable {σ : Type} [Fintype σ] (R : Type u) [CommRing R]
local instance coefficientFormulaDecidableEq (n : ℕ) :
    DecidableEq (LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (n : ℤ)) := Classical.decEq _

theorem homogeneousPolynomialCoefficientsEquiv_apply (n : ℕ)
    (p : homogeneousSubmodule σ R n) (e : LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (n : ℤ)) :
    NonnegativeLaurentPolynomials.MvPolynomial.homogeneousPolynomialCoefficientsEquiv R n p e =
      p.val.coeff ((NonnegativeLaurentPolynomials.MvPolynomial.nonnegativeLaurentWeightEquivDegree n) e).val := rfl

def homogeneousMonomialOfWeight (n : ℕ) (e : LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (n : ℤ)) (r : R) :
    homogeneousSubmodule σ R n :=
  ⟨monomial ((NonnegativeLaurentPolynomials.MvPolynomial.nonnegativeLaurentWeightEquivDegree n) e).val r,
    isHomogeneous_monomial r ((NonnegativeLaurentPolynomials.MvPolynomial.nonnegativeLaurentWeightEquivDegree n) e).property⟩

theorem homogeneousMonomialOfWeight_coefficient (n : ℕ)
    (e f : LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (n : ℤ)) (r : R) :
    NonnegativeLaurentPolynomials.MvPolynomial.homogeneousPolynomialCoefficientsEquiv R n (homogeneousMonomialOfWeight R n e r) f =
      if e = f then r else 0 := by
  classical
  rw [homogeneousPolynomialCoefficientsEquiv_apply]
  change (monomial ((NonnegativeLaurentPolynomials.MvPolynomial.nonnegativeLaurentWeightEquivDegree n) e).val r).coeff
    ((NonnegativeLaurentPolynomials.MvPolynomial.nonnegativeLaurentWeightEquivDegree n) f).val = _
  rw [coeff_monomial]
  have heq : ((NonnegativeLaurentPolynomials.MvPolynomial.nonnegativeLaurentWeightEquivDegree n) e).val =
      ((NonnegativeLaurentPolynomials.MvPolynomial.nonnegativeLaurentWeightEquivDegree n) f).val ↔ e = f := by
    constructor
    · intro h
      exact (NonnegativeLaurentPolynomials.MvPolynomial.nonnegativeLaurentWeightEquivDegree n).injective (Subtype.ext h)
    · rintro rfl
      rfl
  simp only [heq]

theorem homogeneousPolynomial_eq_sum_monomials (n : ℕ) (p : homogeneousSubmodule σ R n) :
    p = ∑ e : LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (n : ℤ),
      homogeneousMonomialOfWeight R n e (NonnegativeLaurentPolynomials.MvPolynomial.homogeneousPolynomialCoefficientsEquiv R n p e) := by
  classical
  apply (NonnegativeLaurentPolynomials.MvPolynomial.homogeneousPolynomialCoefficientsEquiv R n).injective
  funext f
  rw [map_sum, Finset.sum_apply]
  change NonnegativeLaurentPolynomials.MvPolynomial.homogeneousPolynomialCoefficientsEquiv R n p f =
    ∑ e, NonnegativeLaurentPolynomials.MvPolynomial.homogeneousPolynomialCoefficientsEquiv R n
      (homogeneousMonomialOfWeight R n e (NonnegativeLaurentPolynomials.MvPolynomial.homogeneousPolynomialCoefficientsEquiv R n p e)) f
  simp only [homogeneousMonomialOfWeight_coefficient, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.HomogeneousPolynomialCoefficientFormula.MvPolynomial
