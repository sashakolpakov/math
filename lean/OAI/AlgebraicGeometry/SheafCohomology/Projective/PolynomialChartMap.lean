import OAI.AlgebraicGeometry.SheafCohomology.Projective.NonnegativeLaurentPolynomials
import OAI.AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-! # Polynomial Chart Map -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartMap.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-! Dehomogenizing polynomial monomials in a projective chart is a genuine ring homomorphism. -/

universe u
variable {σ : Type} [Fintype σ] {m : ℕ}

 def polynomialChartExponent (a : Fin (m + 1) → σ) :
    (σ →₀ ℕ) →+ LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid (StandardIntersectionRing.MvPolynomial.coordinateTailExponent a) where
  toFun e := ⟨Finsupp.equivFunOnFinite.symm (fun i : {i : σ // i ≠ a 0} => (e i.val : ℤ)), by
    intro i hi
    exact False.elim ((not_lt_of_ge (Int.natCast_nonneg (e i.val))) hi)⟩
  map_zero' := by apply Subtype.ext; ext i; rfl
  map_add' e f := by
    apply Subtype.ext
    ext i
    change ((e i.val + f i.val : ℕ) : ℤ) = (e i.val : ℤ) + (f i.val : ℤ)
    exact Nat.cast_add _ _

def polynomialChartRingHom (R : Type u) [CommRing R] (a : Fin (m + 1) → σ) :
    MvPolynomial σ R →+* AddMonoidAlgebra R (LaurentExponentLocalization.MvPolynomial.laurentExponentSubmonoid (StandardIntersectionRing.MvPolynomial.coordinateTailExponent a)) :=
  AddMonoidAlgebra.mapDomainRingHom R (polynomialChartExponent a)

theorem polynomialChartRingHom_monomial (R : Type u) [CommRing R]
    (a : Fin (m + 1) → σ) (e : σ →₀ ℕ) (r : R) :
    polynomialChartRingHom R a (monomial e r) =
      AddMonoidAlgebra.single (polynomialChartExponent a e) r :=
  AddMonoidAlgebra.mapDomain_single

def nonnegativeLaurentWeightAllowed (a : Fin (m + 1) → σ) (n : ℕ)
    (e : LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (n : ℤ)) :
    {e : LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ (n : ℤ) // e.IsAllowedOn a} :=
  ⟨e.val, fun i hi => False.elim ((not_lt_of_ge (e.property i)) hi)⟩

theorem polynomialChartExponent_eq_homogeneous_symm (a : Fin (m + 1) → σ) (n : ℕ)
    (e : LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (n : ℤ)) :
    polynomialChartExponent a ((NonnegativeLaurentPolynomials.MvPolynomial.nonnegativeLaurentWeightEquivDegree n) e).val =
      (LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv a (n : ℤ)).symm (nonnegativeLaurentWeightAllowed a n e) := by
  apply Subtype.ext
  ext i
  rw [LaurentWeight.MvPolynomial.coordinateLaurentExponentEquiv_symm_apply]
  change ((e.val.val i.val).toNat : ℤ) = e.val.val i.val
  have := e.property i.val
  omega

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartMap.MvPolynomial
