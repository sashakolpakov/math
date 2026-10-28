import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Scalar Pullback -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.ScalarPullback

noncomputable section

/-! Changing the coefficients of an affine polynomial scheme is an
actual scheme pullback, via the native polynomial tensor-product pushout. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem isPullback {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (ι : Type) :
    IsPullback (Spec.map (CommRingCat.ofHom (MvPolynomial.map (σ := ι) f)))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : S →+* MvPolynomial ι S)))
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial ι R)))
      (Spec.map (CommRingCat.ofHom f)) := by
  let := f.toAlgebra
  let : Algebra (MvPolynomial ι R) (MvPolynomial ι S) := MvPolynomial.algebraMvPolynomial
  apply isPullback_SpecMap_of_isPushout
  exact CommRingCat.isPushout_of_isPushout R (MvPolynomial ι R) S (MvPolynomial ι S)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.ScalarPullback
