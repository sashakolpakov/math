import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TwistResidueDuality
import Mathlib.Algebra.MonoidAlgebra.Basic

/-! # Laurent Residue Pairing -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentResiduePairing

noncomputable section

/-! The projective coefficient duality is the coefficient of the
actual product of homogeneous Laurent polynomials. This supplies its
residue normalization before passage to sheaf morphisms. -/

open _root_.MvPolynomial

open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TwistResidueDuality

universe u

variable (σ : Type) [Fintype σ] (C : Type u) [CommRing C]

def exponentCast : (σ →₀ ℕ) →+ (σ →₀ ℤ) :=
  Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)

def polynomialMap : MvPolynomial σ C →ₐ[C] AddMonoidAlgebra C (σ →₀ ℤ) :=
  AddMonoidAlgebra.mapDomainAlgHom C C (exponentCast σ)

def residue : AddMonoidAlgebra C (σ →₀ ℤ) →ₗ[C] C :=
  (Finsupp.lapply (Projective.ResidueTrace.topExponent.{u} σ).val.val).comp
    (AddMonoidAlgebra.coeffLinearEquiv C).toLinearMap

theorem residue_apply (f : AddMonoidAlgebra C (σ →₀ ℤ)) :
    residue σ C f = f.coeff (Projective.ResidueTrace.topExponent.{u} σ).val.val := rfl

def negativeLaurent (m : ℕ) (a : Projective.TwistResidueDuality.NegativeExponent.{u} σ m → C) : AddMonoidAlgebra C (σ →₀ ℤ) :=
  ∑ e : AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (m : ℤ),
    AddMonoidAlgebra.single ((Projective.TwistResidueDuality.complementaryWeightEquiv.{u} σ m).symm e).val.val
      (a ((Projective.TwistResidueDuality.complementaryWeightEquiv.{u} σ m).symm e))

theorem negativeLaurent_coefficient (m : ℕ) (a : Projective.TwistResidueDuality.NegativeExponent.{u} σ m → C)
    (e : AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (m : ℤ)) :
    (negativeLaurent σ C m a).coeff ((Projective.TwistResidueDuality.complementaryWeightEquiv.{u} σ m).symm e).val.val =
      a ((Projective.TwistResidueDuality.complementaryWeightEquiv.{u} σ m).symm e) := by
  classical
  have hinj : Function.Injective
      (fun f : AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (m : ℤ) => ((Projective.TwistResidueDuality.complementaryWeightEquiv.{u} σ m).symm f).val.val) := by
    intro f g h
    exact (Projective.TwistResidueDuality.complementaryWeightEquiv.{u} σ m).symm.injective (Subtype.ext (Subtype.ext h))
  simp only [negativeLaurent, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply, hinj.eq_iff,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem complementary_exponent (m : ℕ) (e : AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (m : ℤ)) :
    -e.val.val + (Projective.ResidueTrace.topExponent.{u} σ).val.val =
      ((Projective.TwistResidueDuality.complementaryWeightEquiv.{u} σ m).symm e).val.val := by
  ext i
  have h := Projective.TwistResidueDuality.complementaryWeight_add σ m ((Projective.TwistResidueDuality.complementaryWeightEquiv.{u} σ m).symm e) i
  rw [Equiv.apply_symm_apply] at h
  simp only [Finsupp.add_apply, Finsupp.neg_apply, Projective.ResidueTrace.topExponent_apply]
  omega

theorem residue_single_mul (m : ℕ) (a : Projective.TwistResidueDuality.NegativeExponent.{u} σ m → C)
    (e : AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (m : ℤ)) (c : C) :
    residue σ C (AddMonoidAlgebra.single e.val.val c * negativeLaurent σ C m a) =
      c * a ((Projective.TwistResidueDuality.complementaryWeightEquiv.{u} σ m).symm e) := by
  rw [residue_apply, AddMonoidAlgebra.coeff_single_mul_apply,
    complementary_exponent, negativeLaurent_coefficient]

theorem exponentCast_nonnegative (m : ℕ) (e : AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (m : ℤ)) :
    exponentCast σ ((AlgebraicGeometry.SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial.nonnegativeLaurentWeightEquivDegree m) e).val = e.val.val := by
  ext i
  change ((e.val.val i).toNat : ℤ) = e.val.val i
  exact Int.toNat_of_nonneg (e.property i)

theorem polynomialMap_monomial (m : ℕ) (e : AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (m : ℤ)) (c : C) :
    polynomialMap σ C (AlgebraicGeometry.SheafCohomology.Projective.HomogeneousPolynomialCoefficientFormula.MvPolynomial.homogeneousMonomialOfWeight C m e c).val =
      AddMonoidAlgebra.single e.val.val c := by
  change AddMonoidAlgebra.mapDomain (exponentCast σ)
    (AddMonoidAlgebra.single ((AlgebraicGeometry.SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial.nonnegativeLaurentWeightEquivDegree m) e).val c) = _
  rw [AddMonoidAlgebra.mapDomain_single, exponentCast_nonnegative]

theorem polynomialMap_homogeneous (m : ℕ) (P : homogeneousSubmodule σ C m) :
    polynomialMap σ C P.val =
      ∑ e : AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (m : ℤ),
        AddMonoidAlgebra.single e.val.val (AlgebraicGeometry.SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial.homogeneousPolynomialCoefficientsEquiv C m P e) := by
  have h := congrArg (fun Q : homogeneousSubmodule σ C m => polynomialMap σ C Q.val)
    (AlgebraicGeometry.SheafCohomology.Projective.HomogeneousPolynomialCoefficientFormula.MvPolynomial.homogeneousPolynomial_eq_sum_monomials C m P)
  simpa only [Submodule.coe_sum, map_sum, polynomialMap_monomial] using h

theorem residue_product (m : ℕ) (a : Projective.TwistResidueDuality.NegativeExponent.{u} σ m → C)
    (P : homogeneousSubmodule σ C m) :
    residue σ C (polynomialMap σ C P.val * negativeLaurent σ C m a) =
      Projective.TwistResidueDuality.polynomialDual σ C m a P := by
  rw [polynomialMap_homogeneous, Finset.sum_mul, map_sum, Projective.TwistResidueDuality.polynomialDual_apply]
  apply Finset.sum_congr rfl
  intro e _
  exact residue_single_mul σ C m a e _

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.LaurentResiduePairing
