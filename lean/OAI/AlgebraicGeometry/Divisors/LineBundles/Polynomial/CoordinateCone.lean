import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.HomogeneousRees
import OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.ConeSymmetric

/-! # Coordinate Cone -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.CoordinateCone.BundleCycles

noncomputable section

/-! # LineBundleCycles: polynomial coordinates inject into the actual variable-ideal normal cone -/

variable {A ι : Type} [CommRing A]

def polynomialCoordinateConeMap : MvPolynomial ι A →+* Normal.Cone.BundleCycles.NormalConeRing (MvPolynomial.idealOfVars ι A) :=
  (Ideal.Quotient.mk (Normal.Cone.BundleCycles.normalConeIdeal (MvPolynomial.idealOfVars ι A))).comp HomogeneousRees.BundleCycles.polynomialHomogeneousRees

theorem polynomialCoordinateConeMap_injective :
    Function.Injective (@polynomialCoordinateConeMap A ι _) := by
  apply (injective_iff_map_eq_zero (polynomialCoordinateConeMap (A := A) (ι := ι))).mpr
  intro p hp
  have h := (ReesCoefficients.BundleCycles.mem_normalConeIdeal_iff _ _).mp (Ideal.Quotient.eq_zero_iff_mem.mp hp)
  apply MvPolynomial.ext
  intro d
  have hd := (MvPolynomial.mem_pow_idealOfVars_iff' (d.degree + 1) _).mp (h d.degree) d
    (Nat.lt_succ_self d.degree)
  rw [HomogeneousRees.BundleCycles.polynomialHomogeneousRees_coeff, MvPolynomial.coeff_homogeneousComponent, ite_eq_left rfl] at hd
  exact hd

theorem polynomialCoordinateConeMap_C (a : A) :
    polynomialCoordinateConeMap (MvPolynomial.C a : MvPolynomial ι A) =
      Ideal.Quotient.mk (Normal.Cone.BundleCycles.normalConeIdeal (MvPolynomial.idealOfVars ι A))
        (algebraMap (MvPolynomial ι A) (reesAlgebra (MvPolynomial.idealOfVars ι A)) (MvPolynomial.C a)) := by
  apply congrArg (Ideal.Quotient.mk _)
  apply Subtype.ext
  change HomogeneousRees.BundleCycles.polynomialHomogeneousMap (MvPolynomial.monomial 0 a) = _
  rw [HomogeneousRees.BundleCycles.polynomialHomogeneousMap_monomial]
  simp only [map_zero, Polynomial.monomial_zero_left]
  rfl

theorem polynomialCoordinateConeMap_X (i : ι) :
    polynomialCoordinateConeMap (MvPolynomial.X i : MvPolynomial ι A) =
      Ideal.Quotient.mk (Normal.Cone.BundleCycles.normalConeIdeal (MvPolynomial.idealOfVars ι A))
        (Normal.ConeSymmetric.BundleCycles.reesDegreeOne (MvPolynomial.idealOfVars ι A)
          ⟨MvPolynomial.X i, Ideal.subset_span ⟨i, rfl⟩⟩) := by
  apply congrArg (Ideal.Quotient.mk _)
  apply Subtype.ext
  change HomogeneousRees.BundleCycles.polynomialHomogeneousMap (MvPolynomial.monomial (Finsupp.single i 1) 1) = _
  rw [HomogeneousRees.BundleCycles.polynomialHomogeneousMap_monomial, Finsupp.degree_single]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.CoordinateCone.BundleCycles
