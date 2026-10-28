import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorBySectionEvaluation
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorSectionFrameCoefficients
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveNormalizedSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OfLEChartSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductPolynomialSections

/-! # Negative Twist Frame Section -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.NegativeTwistFrameSection.Construction

noncomputable section

/-! Normalized sections of a shifted negative twist are coordinate polynomials times its local frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite _root_.MvPolynomial

universe u

local instance negativeTwistCoefficientsMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  AlgebraicGeometry.SheafCohomology.Projective.Monoidal.Scheme.Modules.monoidalCategory X

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

omit [Fintype σ] [LinearOrder σ] in
theorem negativeTwist_shift_frame_section (j : σ) (a n : ℕ) (ha : a ≤ n) :
    (AlgebraicGeometry.SheafCohomology.Projective.TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j a n ha).hom.app
      (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
      ((TensorSectionFrame.Construction.tensorByUnitSection (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a)
        (ProjectiveNormalizedSections.Construction.projectiveTwistUnitSection j n)).app (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
          (AlgebraicGeometry.SheafCohomology.Projective.DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j a)) =
    (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (n - a)).presheaf.map
      (homOfLE (le_top : AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j ≤ ⊤)).op
      (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j (n - a)) := by
  let M := AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a
  let e := AlgebraicGeometry.SheafCohomology.Projective.TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j a n ha
  let m := AlgebraicGeometry.SheafCohomology.Projective.DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j a
  let t : AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)) ⟶
      AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n :=
    (AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv _).symm (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower j n)
  have ht := TensorBySectionEvaluation.Construction.tensorByUnitSection_local_section M t (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j) m
  have hu := AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Gluing.moduleSectionHomEquiv_restrict (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
    t (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j)
  rw [Equiv.apply_symm_apply] at hu
  have h := AlgebraicGeometry.SheafCohomology.Projective.OfLEChartSections.MvPolynomial.coordinateHyperplaneTwistShiftOfLE_chart_section (R := R) (σ := σ) j a n ha
  exact (congrArg (e.hom.app (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j))
    (ht.trans (congrArg (AlgebraicGeometry.SheafCohomology.Projective.TensorSections.tensorSection M _ (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j) m) hu.symm))).trans h

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.NegativeTwistFrameSection.Construction
