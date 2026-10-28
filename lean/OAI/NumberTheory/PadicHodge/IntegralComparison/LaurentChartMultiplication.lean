import OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentPolynomialAction
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartHomogeneous

/-! # Laurent Chart Multiplication -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentChartMultiplication

noncomputable section

/-! Multiplication in a projective chart becomes the explicit homogeneous
Laurent polynomial action under the original exponent reindexing. -/

open _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentPolynomialAction

universe u

variable {σ : Type} [Fintype σ] (C : Type u) [CommRing C]

def reindex (d : ℤ) {n : ℕ} (a : Fin (n + 1) → σ) :
    AddMonoidAlgebra C (AlgebraicGeometry.SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid (AlgebraicGeometry.SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent a)) ≃ₗ[C]
      AddMonoidAlgebra C (LaurentPolynomialAction.Allowed d a) :=
  AddMonoidAlgebra.mapDomainLinearEquiv C C (AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a d)

omit [Fintype σ] in
theorem reindex_single (d : ℤ) {n : ℕ} (a : Fin (n + 1) → σ)
    (f : AlgebraicGeometry.SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid (AlgebraicGeometry.SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent a)) (c : C) :
    reindex C d a (AddMonoidAlgebra.single f c) =
      AddMonoidAlgebra.single (AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a d f) c :=
  AddMonoidAlgebra.mapDomainLinearEquiv_single _ _ _

omit [Fintype σ] in
theorem exponent_add (m : ℕ) (d : ℤ) {n : ℕ} (a : Fin (n + 1) → σ)
    (e : AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (m : ℤ))
    (f : AlgebraicGeometry.SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid (AlgebraicGeometry.SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent a)) :
    AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a ((m : ℤ) + d)
        ((AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a (m : ℤ)).symm (AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.nonnegativeLaurentWeightAllowed a m e) + f) =
      LaurentPolynomialAction.shift m d a e (AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a d f) := by
  apply (AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a ((m : ℤ) + d)).symm.injective
  rw [Equiv.symm_apply_apply]
  apply Subtype.ext
  ext i
  rw [AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_symm_apply]
  change ((AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a (m : ℤ)).symm
      (AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.nonnegativeLaurentWeightAllowed a m e)).val i + f.val i =
    e.val.val i.val + (AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a d f).val.val i.val
  rw [AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_symm_apply,
    AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_apply_of_ne a d f i.val i.property]
  rfl

omit [Fintype σ] in
theorem reindex_single_mul (m : ℕ) (d : ℤ) {n : ℕ} (a : Fin (n + 1) → σ)
    (e : AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (m : ℤ)) (c : C)
    (x : AddMonoidAlgebra C (AlgebraicGeometry.SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid (AlgebraicGeometry.SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent a))) :
    reindex C ((m : ℤ) + d) a
        (AddMonoidAlgebra.single ((AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a (m : ℤ)).symm
          (AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.nonnegativeLaurentWeightAllowed a m e)) c * x) =
      c • LaurentPolynomialAction.monomial C m d a e (reindex C d a x) := by
  have h : (reindex C ((m : ℤ) + d) a).toLinearMap.comp
      (LinearMap.mulLeft C (AddMonoidAlgebra.single
        ((AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a (m : ℤ)).symm (AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.nonnegativeLaurentWeightAllowed a m e)) c)) =
      c • (LaurentPolynomialAction.monomial C m d a e).comp (reindex C d a).toLinearMap := by
    apply AddMonoidAlgebra.lhom_ext'
    intro f
    apply LinearMap.ext
    intro r
    simp only [LinearMap.comp_apply, AddMonoidAlgebra.lsingle_apply, LinearMap.mulLeft_apply,
      LinearMap.smul_apply, LinearEquiv.coe_coe, AddMonoidAlgebra.single_mul_single,
      reindex_single, LaurentPolynomialAction.monomial, AddMonoidAlgebra.mapDomainLinearMap_single,
      AddMonoidAlgebra.smul_single, smul_eq_mul, exponent_add]
  exact LinearMap.congr_fun h x

theorem reindex_polynomial_mul (m : ℕ) (d : ℤ) {n : ℕ} (a : Fin (n + 1) → σ)
    (P : homogeneousSubmodule σ C m)
    (x : AddMonoidAlgebra C (AlgebraicGeometry.SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid (AlgebraicGeometry.SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent a))) :
    reindex C ((m : ℤ) + d) a (AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartMap.MvPolynomial.polynomialChartRingHom C a P.val * x) =
      LaurentPolynomialAction.polynomial C m d a P (reindex C d a x) := by
  classical
  simp only [AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartHomogeneous.MvPolynomial.polynomialChartRingHom_homogeneous, Finset.sum_mul, map_sum,
    reindex_single_mul, LaurentPolynomialAction.polynomial, LinearMap.sum_apply, LinearMap.smul_apply]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentChartMultiplication
