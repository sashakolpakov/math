import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.CoordinateCone
import OAI.AlgebraicGeometry.Divisors.LineBundles.SpecialFiber

/-! # Coordinate Deformation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.CoordinateDeformation.BundleCycles

noncomputable section

/-! The coordinate algebra maps to its actual deformation by sending
each variable x to x/t. The zero-fiber map is the proved normal-cone map. -/

variable {A ι : Type} [CommRing A]

def polynomialCoordinateDeformationMap :
    MvPolynomial ι A →+* Deformation.Iff.BundleCycles.deformationAlgebra (MvPolynomial.idealOfVars ι A) :=
  (Deformation.Iff.BundleCycles.reesToDeformation (MvPolynomial.idealOfVars ι A)).toRingHom.comp HomogeneousRees.BundleCycles.polynomialHomogeneousRees

theorem polynomialCoordinateDeformationMap_mod_parameter :
    (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (MvPolynomial.idealOfVars ι A))).comp
        polynomialCoordinateDeformationMap =
      (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv (MvPolynomial.idealOfVars ι A)).toRingHom.comp CoordinateCone.BundleCycles.polynomialCoordinateConeMap := by
  apply RingHom.ext
  intro a
  exact (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv_mk (MvPolynomial.idealOfVars ι A) (HomogeneousRees.BundleCycles.polynomialHomogeneousRees a)).symm

theorem polynomialCoordinateDeformationMap_C (a : A) :
    polynomialCoordinateDeformationMap (MvPolynomial.C a : MvPolynomial ι A) =
      algebraMap (MvPolynomial ι A) (Deformation.Iff.BundleCycles.deformationAlgebra (MvPolynomial.idealOfVars ι A)) (MvPolynomial.C a) := by
  have h : HomogeneousRees.BundleCycles.polynomialHomogeneousRees (MvPolynomial.C a : MvPolynomial ι A) =
      algebraMap (MvPolynomial ι A) (reesAlgebra (MvPolynomial.idealOfVars ι A)) (MvPolynomial.C a) := by
    apply Subtype.ext
    exact MvPolynomial.eval₂Hom_C _ _ a
  change Deformation.Iff.BundleCycles.reesToDeformation _ (HomogeneousRees.BundleCycles.polynomialHomogeneousRees (MvPolynomial.C a)) = _
  rw [h]
  exact (Deformation.Iff.BundleCycles.reesToDeformation (MvPolynomial.idealOfVars ι A)).commutes _

theorem polynomialCoordinateDeformationMap_X (i : ι) :
    polynomialCoordinateDeformationMap (MvPolynomial.X i : MvPolynomial ι A) =
      Deformation.Iff.BundleCycles.deformationMonomial (MvPolynomial.idealOfVars ι A) (-1) (MvPolynomial.X i)
        (by simpa using (Ideal.subset_span (s := Set.range (MvPolynomial.X : ι → MvPolynomial ι A)) ⟨i, rfl⟩)) := by
  apply Subtype.ext
  change LaurentPolynomial.invert (Polynomial.toLaurent (HomogeneousRees.BundleCycles.polynomialHomogeneousMap (MvPolynomial.X i))) = _
  have h : HomogeneousRees.BundleCycles.polynomialHomogeneousMap (MvPolynomial.X i : MvPolynomial ι A) =
      Polynomial.monomial 1 (MvPolynomial.X i) := MvPolynomial.eval₂Hom_X' _ _ i
  rw [h, Polynomial.toLaurent_C_mul_T, map_mul, LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
  exact (LaurentPolynomial.single_eq_C_mul_T _ _).symm

theorem polynomialCoordinateDeformationMap_monomial_val (d : ι →₀ ℕ) (a : A) :
    (polynomialCoordinateDeformationMap (MvPolynomial.monomial d a)).val =
      AddMonoidAlgebra.single (-(d.degree : ℤ)) (MvPolynomial.monomial d a) := by
  change LaurentPolynomial.invert (Polynomial.toLaurent (HomogeneousRees.BundleCycles.polynomialHomogeneousMap (MvPolynomial.monomial d a))) = _
  rw [HomogeneousRees.BundleCycles.polynomialHomogeneousMap_monomial, Polynomial.toLaurent_C_mul_T, map_mul,
    LaurentPolynomial.invert_C, LaurentPolynomial.invert_T]
  exact (LaurentPolynomial.single_eq_C_mul_T _ _).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.CoordinateDeformation.BundleCycles
