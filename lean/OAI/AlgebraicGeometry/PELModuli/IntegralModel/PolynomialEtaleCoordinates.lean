import OAI.AlgebraicGeometry.PELModuli.IntegralModel.SmoothEtaleDifferentials
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Polynomial Etale Coordinates -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolynomialEtaleCoordinates

noncomputable section

/-! A differential basis consisting of polynomial coordinates gives
an actual etale coordinate map on a smooth algebra. -/

open TensorProduct KaehlerDifferential _root_.Module

theorem polynomial_differential_map_bijective
    (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    (ι : Type*) [Algebra (MvPolynomial ι R) B] [IsScalarTower R (MvPolynomial ι R) B]
    (b : Basis ι B Ω[B⁄R])
    (hb : ∀ i, b i = D R B (algebraMap (MvPolynomial ι R) B (MvPolynomial.X i))) :
    Function.Bijective (mapBaseChange R (MvPolynomial ι R) B) := by
  let a := (mvPolynomialBasis R ι).baseChange B
  let e := a.equiv b (Equiv.refl ι)
  have he : mapBaseChange R (MvPolynomial ι R) B = e.toLinearMap := by
    apply a.ext
    intro i
    rw [LinearEquiv.coe_coe, Basis.equiv_apply]
    simp only [a, Basis.baseChange_apply, mvPolynomialBasis_apply,
      mapBaseChange_tmul, one_smul, map_D, hb, Equiv.refl_apply]
  exact he ▸ e.bijective

theorem polynomial_coordinates_formallyEtale
    (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    (ι : Type*) [Algebra (MvPolynomial ι R) B] [IsScalarTower R (MvPolynomial ι R) B]
    [Algebra.FormallySmooth R B] (b : Basis ι B Ω[B⁄R])
    (hb : ∀ i, b i = D R B (algebraMap (MvPolynomial ι R) B (MvPolynomial.X i))) :
    Algebra.FormallyEtale (MvPolynomial ι R) B :=
  SmoothEtaleDifferentials.formallyEtale_of_smooth_differential_comparison R (MvPolynomial ι R) B
    (polynomial_differential_map_bijective R B ι b hb)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PolynomialEtaleCoordinates
