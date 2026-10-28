import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartHomogeneous

/-! # Polynomial Chart Injective -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartInjective.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-! A homogeneous polynomial of fixed degree is determined on any coordinate chart. -/

universe u
variable {σ : Type} [Fintype σ] (R : Type u) [CommRing R] {m : ℕ}

theorem polynomialChart_homogeneous_coefficient (a : Fin (m + 1) → σ) (n : ℕ)
    (p : homogeneousSubmodule σ R n) (e : LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (n : ℤ)) :
    (PolynomialChartMap.MvPolynomial.polynomialChartRingHom R a p.val).coeff
        ((LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a (n : ℤ)).symm
          (PolynomialChartMap.MvPolynomial.nonnegativeLaurentWeightAllowed a n e)) =
      NonnegativeLaurentPolynomials.MvPolynomial.homogeneousPolynomialCoefficientsEquiv R n p e := by
  classical
  rw [PolynomialChartHomogeneous.MvPolynomial.polynomialChartRingHom_homogeneous, AddMonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single e]
  · simp
  · intro f _ hfe
    have hne : (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a (n : ℤ)).symm
        (PolynomialChartMap.MvPolynomial.nonnegativeLaurentWeightAllowed a n f) ≠
        (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a (n : ℤ)).symm
          (PolynomialChartMap.MvPolynomial.nonnegativeLaurentWeightAllowed a n e) := by
      intro h
      have hallowed := (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a (n : ℤ)).symm.injective h
      have hweight := congrArg
        (fun t : {w : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ (n : ℤ) // w.IsAllowedOn a} => t.val)
        hallowed
      exact hfe (Subtype.ext hweight)
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, ite_eq_right hne]
  · simp

theorem polynomialChartRingHom_injective_homogeneous (a : Fin (m + 1) → σ) (n : ℕ) :
    Function.Injective (fun p : homogeneousSubmodule σ R n =>
      PolynomialChartMap.MvPolynomial.polynomialChartRingHom R a p.val) := by
  intro p q h
  apply (NonnegativeLaurentPolynomials.MvPolynomial.homogeneousPolynomialCoefficientsEquiv R n).injective
  funext e
  have he := congrArg (fun f => AddMonoidAlgebra.coeff f
    ((LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a (n : ℤ)).symm
      (PolynomialChartMap.MvPolynomial.nonnegativeLaurentWeightAllowed a n e))) h
  simpa only [polynomialChart_homogeneous_coefficient] using he

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartInjective.MvPolynomial
