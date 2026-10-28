import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistFrameSection
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistPolynomialChart
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorBySectionEvaluation
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionFrameCoefficients
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NormalizedSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OfLEChartSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductPolynomialSections

/-! # Negative Twist Coefficients -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistCoefficients.Dimension

noncomputable section

/-! Normalized sections of a shifted negative twist are coordinate polynomials times its local frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite _root_.MvPolynomial

universe u

local instance negativeTwistNormalizedCoefficientsMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem negativeTwist_tensorSectionGlobalCoefficient (j : σ) (a n : ℕ) (ha : a ≤ n)
    (x : Γ(TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⊗
      TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower j n, ⊤)) :
    ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionRestriction.Construction.tensorSectionGlobalCoefficient (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a)
      (UnitSection.Dimension.projectiveTwistUnitSection j n) (MvPolynomialClosure.MvPolynomial.coordinateOpen j) x =
    ChartPolynomialMap.Dimension.projectiveChartPolynomialMap j (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistPolynomialSectionEquiv j a n ha x).val •
      DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j a := by
  let M := TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a
  let e := TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j a n ha
  let s := TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j (n - a)
  let m := DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j a
  have h := ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionFrameCoefficients.Construction.tensorSectionGlobalCoefficient_of_frame M (UnitSection.Dimension.projectiveTwistUnitSection j n)
    (MvPolynomialClosure.MvPolynomial.coordinateOpen j) e (PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSheafPowerOverFrame j j (n - a)) s
    (PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSectionPower_coefficient_self j (n - a)) m
    (NegativeTwistFrameSection.Dimension.negativeTwist_shift_frame_section (R := R) j a n ha) x
  exact h.trans (congrArg (fun r => r • m)
    (NegativeTwistPolynomialChart.Dimension.negativeTwistPolynomialSectionEquiv_chartCoefficient (R := R) j a n ha x).symm)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistCoefficients.Dimension
