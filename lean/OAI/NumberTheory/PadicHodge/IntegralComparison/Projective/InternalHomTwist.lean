import OAI.NumberTheory.PadicHodge.IntegralComparison.LineInternalHomTensor
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PairedTwistEquivalence

/-! # Internal Hom Twist -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.InternalHomTwist

noncomputable section

/-! The internal Hom between ordered negative projective twists is the
actual positive twist of the degree difference. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial MonoidalCategory

set_option backward.isDefEq.respectTransparency false

open OAI.NumberTheory.PadicHodge.IntegralComparison.LineInternalHomTensor

universe u

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ]

attribute [local instance] MvPolynomial.gradedAlgebra

local instance (X : Scheme.{u}) : MonoidalCategory X.Modules := AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

def negativeIso (j : σ) (a b : ℕ) (hba : b ≤ a) :
    ArithmeticGeometry.OrdinaryLocus.Openness.SheafHomModule.Construction.sheafHomModule (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a)
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) ≅
        AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (a - b) :=
  LineInternalHomTensor.inverseTensorIso _ _ _
    (LineInternalHomTensor.isLineBundle_of_isInvertible (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible j a))
    (LineInternalHomTensor.isLineBundle_of_isInvertible (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_isInvertible j b))
    (AlgebraicGeometry.SheafCohomology.Projective.TwistShiftIso.MvPolynomial.coordinateHyperplanePowerCancellationIso j a) ≪≫
      AlgebraicGeometry.SheafCohomology.Projective.TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE j b a hba

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.InternalHomTwist
