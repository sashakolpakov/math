import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorBySectionEvaluation
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionFrameCoefficients
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NormalizedSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OfLEChartSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductPolynomialSections

/-! # Negative Twist Frame Section -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistFrameSection.Dimension

noncomputable section

/-! Normalized sections of a shifted negative twist are coordinate polynomials times its local frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite _root_.MvPolynomial

universe u

local instance negativeTwistCoefficientsMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

omit [Fintype σ] [LinearOrder σ] in
theorem negativeTwist_shift_frame_section (j : σ) (a n : ℕ) (ha : a ≤ n) :
    (TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j a n ha).hom.app
      (MvPolynomialClosure.MvPolynomial.coordinateOpen j)
      ((ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionFrame.Construction.tensorByUnitSection (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a)
        (UnitSection.Dimension.projectiveTwistUnitSection j n)).app (MvPolynomialClosure.MvPolynomial.coordinateOpen j)
          (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j a)) =
    (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (n - a)).presheaf.map
      (homOfLE (le_top : MvPolynomialClosure.MvPolynomial.coordinateOpen j ≤ ⊤)).op
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j (n - a)) := by
  let M := TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a
  let e := TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j a n ha
  let m := DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j a
  let t : Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)) ⟶
      TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n :=
    (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv _).symm (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower j n)
  have ht := ArithmeticGeometry.OrdinaryLocus.Openness.TensorBySectionEvaluation.Construction.tensorByUnitSection_local_section M t (MvPolynomialClosure.MvPolynomial.coordinateOpen j) m
  have hu := AbelianModuli.HilbertConstruction.Section.Gluing.moduleSectionHomEquiv_restrict (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
    t (MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  rw [Equiv.apply_symm_apply] at hu
  have h := OfLEChartSections.MvPolynomial.coordinateHyperplaneTwistShiftOfLE_chart_section (R := R) (σ := σ) j a n ha
  exact (congrArg (e.hom.app (MvPolynomialClosure.MvPolynomial.coordinateOpen j))
    (ht.trans (congrArg (TensorSections.tensorSection M _ (MvPolynomialClosure.MvPolynomial.coordinateOpen j) m) hu.symm))).trans h

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistFrameSection.Dimension
