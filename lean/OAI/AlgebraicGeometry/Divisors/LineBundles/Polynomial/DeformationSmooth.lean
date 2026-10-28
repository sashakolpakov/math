import OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.DeformationEquiv
import Mathlib.RingTheory.Smooth.Basic

/-! # Deformation Smooth -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.DeformationSmooth.BundleCycles

noncomputable section

/-! The coordinate-origin deformation is smooth over its actual
coefficient ring when the coordinate set is finite. -/

variable (A ι : Type) [CommRing A]

def polynomialDeformationAlgEquiv : Polynomial (MvPolynomial ι A) ≃ₐ[A]
    Deformation.Iff.BundleCycles.deformationAlgebra (MvPolynomial.idealOfVars ι A) :=
  { DeformationEquiv.BundleCycles.polynomialDeformationEquiv A ι with
    commutes' := fun a => by
      change Polynomial.eval₂RingHom CoordinateDeformation.BundleCycles.polynomialCoordinateDeformationMap
        (Deformation.Iff.BundleCycles.deformationParameter (MvPolynomial.idealOfVars ι A)) (Polynomial.C (MvPolynomial.C a)) = _
      rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, CoordinateDeformation.BundleCycles.polynomialCoordinateDeformationMap_C]
      rfl }

theorem polynomialDeformation_smooth [Finite ι] :
    Algebra.Smooth A (Deformation.Iff.BundleCycles.deformationAlgebra (MvPolynomial.idealOfVars ι A)) := by
  let : Algebra.Smooth A (MvPolynomial ι A) := {}
  let : Algebra.Smooth (MvPolynomial ι A) (Polynomial (MvPolynomial ι A)) := {}
  let : Algebra.Smooth A (Polynomial (MvPolynomial ι A)) :=
    Algebra.Smooth.comp A (MvPolynomial ι A) (Polynomial (MvPolynomial ι A))
  exact Algebra.Smooth.of_equiv (R := A) (A := Polynomial (MvPolynomial ι A))
    (B := Deformation.Iff.BundleCycles.deformationAlgebra (MvPolynomial.idealOfVars ι A)) (polynomialDeformationAlgEquiv A ι)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Polynomial.DeformationSmooth.BundleCycles
