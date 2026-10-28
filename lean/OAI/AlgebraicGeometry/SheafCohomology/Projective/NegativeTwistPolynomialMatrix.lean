import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomPolynomials
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoproductMatrixComponents

/-! # Negative Twist Polynomial Matrix -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistPolynomialMatrix

noncomputable section

open _root_.MvPolynomial

/-! Faithful polynomial matrices for maps between finite sums of ordered negative twists. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry OAI.AlgebraicGeometry.SheafCohomology.Projective.CoproductMatrixComponents
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance polynomialMatrixBiproducts (X : Scheme.{u}) :
    HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts

def coordinateNegativeTwistPolynomialMatrix (j : σ) {r s : ℕ}
    (d : Fin r → ℕ) (e : Fin s → ℕ) (hde : ∀ i k, d i ≤ e k)
    (f : (∐ fun k => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (e k)) ⟶
      (∐ fun i => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i)))
    (i : Fin r) (k : Fin s) :
    homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) (e k - d i) :=
  CoproductMatrixComponents.finiteCoproductEncodedMatrix
    (fun k => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (e k))
    (fun i => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i))
    (fun i k => NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials j (e k) (d i) (hde i k)) f i k

theorem coordinateNegativeTwistPolynomialMatrix_injective (j : σ) {r s : ℕ}
    (d : Fin r → ℕ) (e : Fin s → ℕ) (hde : ∀ i k, d i ≤ e k) :
    Function.Injective (coordinateNegativeTwistPolynomialMatrix (R := R) j d e hde) :=
  CoproductMatrixComponents.finiteCoproductEncodedMatrix_injective
    (fun k => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (e k))
    (fun i => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (d i))
    (fun i k => NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials j (e k) (d i) (hde i k))

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistPolynomialMatrix
