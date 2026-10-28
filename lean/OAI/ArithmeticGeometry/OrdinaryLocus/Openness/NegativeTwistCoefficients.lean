import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.NegativeTwistFrameSection
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.NegativeTwistPolynomialChart
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorBySectionEvaluation
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionFrameCoefficients
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveNormalizedSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OfLEChartSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductPolynomialSections

/-! # Negative Twist Coefficients -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.NegativeTwistCoefficients.Construction

noncomputable section

/-! Normalized sections of a shifted negative twist are coordinate polynomials times its local frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite _root_.MvPolynomial

universe u

local instance negativeTwistNormalizedCoefficientsMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem negativeTwist_tensorSectionGlobalCoefficient (j : σ) (a n : ℕ) (ha : a ≤ n)
    (x : Γ(AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⊗
      AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n, ⊤)) :
    TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a)
      (ProjectiveNormalizedSections.Construction.projectiveTwistUnitSection j n) (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j) x =
    ProjectiveChartPolynomialMap.Construction.projectiveChartPolynomialMap j (AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistPolynomialSectionEquiv j a n ha x).val •
      AlgebraicGeometry.SheafCohomology.Projective.DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j a := by
  let M := AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a
  let e := AlgebraicGeometry.SheafCohomology.Projective.TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j a n ha
  let s := AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j (n - a)
  let m := AlgebraicGeometry.SheafCohomology.Projective.DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j a
  have h := TensorSectionFrameCoefficients.Construction.tensorSectionGlobalCoefficient_of_frame M (ProjectiveNormalizedSections.Construction.projectiveTwistUnitSection j n)
    (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j) e (AlgebraicGeometry.SheafCohomology.Projective.PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSheafPowerOverFrame j j (n - a)) s
    (AlgebraicGeometry.SheafCohomology.Projective.PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSectionPower_coefficient_self j (n - a)) m
    (NegativeTwistFrameSection.Construction.negativeTwist_shift_frame_section (R := R) j a n ha) x
  exact h.trans (congrArg (fun r => r • m)
    (NegativeTwistPolynomialChart.Construction.negativeTwistPolynomialSectionEquiv_chartCoefficient (R := R) j a n ha x).symm)

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.NegativeTwistCoefficients.Construction
