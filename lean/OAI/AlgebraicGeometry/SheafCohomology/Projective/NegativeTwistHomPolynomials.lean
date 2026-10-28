import OAI.AlgebraicGeometry.SheafCohomology.Projective.DegreeZeroPolynomials
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PairedTwistEquivalence
import OAI.AlgebraicGeometry.SheafCohomology.Projective.UnitHomTopSections

/-! # Negative Twist Hom Polynomials -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomPolynomials.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-! Maps between ordered negative twists are actual homogeneous polynomials. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory OAI.AlgebraicGeometry.SheafCohomology.Projective.UnitHomTopSections
universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance negativeTwistHomMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules := Monoidal.Scheme.Modules.monoidalCategory X

def coordinateNegativeTwistHomEquivPolynomials (j : σ) (a b : ℕ) (hba : b ≤ a) :
    (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) ≃
      homogeneousSubmodule σ Γ(Spec (CommRingCat.of R), ⊤) (a - b) := by
  let X := Proj (homogeneousSubmodule σ R)
  let Na := TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a
  let Nb := TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b
  let Pa := TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j a
  let Pab := TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (a - b)
  let E := PairedTwistEquivalence.MvPolynomial.coordinateHyperplaneTwistPairEquivalence (R := R) j a
  let e₀ : (Na ⟶ Nb) ≃ (Na ⊗ Pa ⟶ Nb ⊗ Pa) := E.fullyFaithfulFunctor.homEquiv
  let e₁ : (Na ⊗ Pa ⟶ Nb ⊗ Pa) ≃ (Invertible.Scheme.Modules.unitObj X ⟶ Pab) :=
    Iso.homCongr (TwistShiftIso.MvPolynomial.coordinateHyperplanePowerCancellationIso (R := R) j a ≪≫
      TensorSections.monoidalUnitObjIso X)
      (TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j b a hba)
  exact e₀.trans (e₁.trans ((UnitHomTopSections.unitHomTopSectionsEquiv Pab).trans
    (DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j (a - b)).toEquiv))

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomPolynomials.MvPolynomial
