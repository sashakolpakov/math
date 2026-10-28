import OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.ResidueTrace
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HomogeneousPolynomialCoefficientFormula
import OAI.AlgebraicGeometry.SheafCohomology.Projective.DegreeZeroPolynomials
import Mathlib.LinearAlgebra.Dual.Defs

/-! # Twist Residue Duality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TwistResidueDuality

noncomputable section

/-! Complementary Laurent monomials identify the original top
cohomology of O(-m-d-1) with the linear dual of the original global
sections of O(m). The pairing is given by its explicit residue
coefficient formula. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable (σ : Type) [Fintype σ]

abbrev NegativeExponent (m : ℕ) :=
  {e : AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ (-(m : ℤ) - (Fintype.card σ : ℤ)) //
    e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))}

def complementaryWeightEquiv (m : ℕ) : NegativeExponent.{u} σ m ≃ AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (m : ℤ) :=
  (AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentCount.MvPolynomial.liftedFullNegativeLaurentWeightEquiv.{u} (σ := σ) (-(m : ℤ) - (Fintype.card σ : ℤ))).trans
    ((AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentCount.MvPolynomial.fullNegativeLaurentWeightEquivDegree (σ := σ) m).trans
      (AlgebraicGeometry.SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial.nonnegativeLaurentWeightEquivDegree (σ := σ) m).symm)

theorem complementaryWeight_add (m : ℕ) (e : NegativeExponent.{u} σ m) (i : σ) :
    e.val.val i + (complementaryWeightEquiv σ m e).val.val i = -1 := by
  have hi : e.val.val i < 0 := by
    have h : ULift.up i ∈ e.val.liftedNegativeSupport := by rw [e.property]; trivial
    exact h
  change e.val.val i + ((-e.val.val i - 1).toNat : ℤ) = -1
  omega

variable (C : Type u) [CommRing C]

def polynomialDual (m : ℕ) :
    (NegativeExponent.{u} σ m → C) ≃ₗ[C] Module.Dual C (homogeneousSubmodule σ C m) :=
  (LinearEquiv.piCongrLeft' C (fun _ : NegativeExponent.{u} σ m => C)
    (complementaryWeightEquiv σ m)).trans
      ((Module.Basis.ofEquivFun (AlgebraicGeometry.SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial.homogeneousPolynomialCoefficientsEquiv C m)).constr C)

theorem polynomialDual_apply (m : ℕ) (a : NegativeExponent.{u} σ m → C)
    (P : homogeneousSubmodule σ C m) :
    polynomialDual σ C m a P =
      ∑ e : AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (m : ℤ),
        AlgebraicGeometry.SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial.homogeneousPolynomialCoefficientsEquiv C m P e *
          a ((complementaryWeightEquiv σ m).symm e) := by
  classical
  change ((Module.Basis.ofEquivFun (AlgebraicGeometry.SheafCohomology.Projective.NonnegativeLaurentPolynomials.MvPolynomial.homogeneousPolynomialCoefficientsEquiv C m)).constr C
    (fun e => a ((complementaryWeightEquiv σ m).symm e))) P = _
  rw [Module.Basis.constr_apply_fintype]
  simp only [Module.Basis.equivFun_ofEquivFun, smul_eq_mul]

theorem polynomialDual_monomial (m : ℕ) (a : NegativeExponent.{u} σ m → C)
    (e : AlgebraicGeometry.SheafCohomology.Projective.LaurentZeroCoefficients.MvPolynomial.NonnegativeLaurentWeight σ (m : ℤ)) (c : C) :
    polynomialDual σ C m a (AlgebraicGeometry.SheafCohomology.Projective.HomogeneousPolynomialCoefficientFormula.MvPolynomial.homogeneousMonomialOfWeight C m e c) =
      c * a ((complementaryWeightEquiv σ m).symm e) := by
  classical
  rw [polynomialDual_apply]
  simp only [AlgebraicGeometry.SheafCohomology.Projective.HomogeneousPolynomialCoefficientFormula.MvPolynomial.homogeneousMonomialOfWeight_coefficient, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]

def polynomialDualCard (m c : ℕ) (hc : Fintype.card σ = c) :
    ({e : AlgebraicGeometry.SheafCohomology.Projective.LaurentWeight.MvPolynomial.HomogeneousLaurentExponent σ (-(m : ℤ) - (c : ℤ)) //
        e.liftedNegativeSupport = (Set.univ : Set (ULift.{u} σ))} → C)
      ≃ₗ[C] Module.Dual C (homogeneousSubmodule σ C m) := by
  subst c
  exact polynomialDual σ C m

variable (R : Type u) [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

def laurentTopDual (n m : ℕ) (j : Fin (n + 2)) :
    (AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplex (R := R) j
      (-(m : ℤ) - ((n + 2 : ℕ) : ℤ))).homology (n + 1)
        ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
          Module.Dual Γ(Spec (CommRingCat.of R), ⊤)
            (homogeneousSubmodule (Fin (n + 2)) Γ(Spec (CommRingCat.of R), ⊤) m) :=
  (AlgebraicGeometry.SheafCohomology.Projective.NegativeLaurentTop.MvPolynomial.coordinateHomogeneousLaurentTopHomologyEquivCoefficients
    (R := R) j (-(m : ℤ) - ((n + 2 : ℕ) : ℤ)) n (by simp)).trans
      (polynomialDualCard (Fin (n + 2)) Γ(Spec (CommRingCat.of R), ⊤) m (n + 2) (by simp))

def topDual (n m : ℕ) (j : Fin (n + 2)) :
    (AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
      (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2)))
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j (-(m : ℤ) - ((n + 2 : ℕ) : ℤ)))
      (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n + 2)))).homology (n + 1)
        ≃ₗ[Γ(Spec (CommRingCat.of R), ⊤)]
          Module.Dual Γ(Spec (CommRingCat.of R), ⊤)
            ((AlgebraicGeometry.SheafCohomology.Projective.OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
              (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := Fin (n + 2)))
              (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)
              (AlgebraicGeometry.SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := Fin (n + 2)))).homology 0) :=
  (HomologicalComplex.homologyMapIso
    ((AlgebraicGeometry.SheafCohomology.Projective.TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechComplexIso (R := R) j
      (-(m : ℤ) - ((n + 2 : ℕ) : ℤ))) ≪≫
      (AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechComplexIso (R := R) j
        (-(m : ℤ) - ((n + 2 : ℕ) : ℤ)))) (n + 1)).toLinearEquiv.trans
    ((laurentTopDual R n m j).trans (AlgebraicGeometry.SheafCohomology.Projective.DegreeZeroPolynomials.MvPolynomial.coordinateTwistHZeroLinearEquivPolynomials (R := R) j m).dualMap)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.TwistResidueDuality
