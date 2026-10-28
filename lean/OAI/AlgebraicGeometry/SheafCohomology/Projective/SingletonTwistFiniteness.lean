import OAI.AlgebraicGeometry.SheafCohomology.Projective.SingletonWeights
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechWeights
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteHomologyOfTerm

/-! # Singleton Twist Finiteness -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.SingletonTwistFiniteness.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-! Finiteness of twist cohomology when projective space has at most one coordinate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem coordinateHyperplaneTwist_homology_module_finite_of_subsingleton
    [Fintype σ] [LinearOrder σ] [Subsingleton σ] [IsNoetherianRing R]
    (j : σ) (d : ℤ) (q : ℕ) :
    Module.Finite
      Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
      ((OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
        (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))).homology q) := by
  let A := Γ(Spec (CommRingCat.of R), (⊤ : (Spec (CommRingCat.of R)).Opens))
  let K := OrderedBaseCech.Scheme.Modules.orderedBaseCechComplex
    (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
    (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)
    (StandardCech.MvPolynomial.coordinateOpenCover (R := R) (σ := σ))
  let : IsNoetherianRing A := isNoetherianRing_of_ringEquiv R
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
  let : Module.Finite A
      (LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject (R := R) (σ := σ) d q) :=
    SingletonWeights.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObject_module_finite_of_subsingleton d q
  let e := TwistCech.MvPolynomial.coordinateHyperplaneTwistOrderedBaseCechObjectIsoUnit (R := R) j d q ≪≫
    LaurentCechData.MvPolynomial.coordinateHomogeneousLaurentOrderedCechObjectIso (R := R) (σ := σ) d q
  let : Module.Finite A (K.X q) := Module.Finite.equiv e.symm.toLinearEquiv
  exact FiniteHomologyOfTerm.moduleFinite_homology_of_moduleFinite_term K q

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.SingletonTwistFiniteness.MvPolynomial
