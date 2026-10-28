import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.ProjectiveChartPolynomialMap
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductPolynomialSections

/-! # Negative Twist Polynomial Chart -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.NegativeTwistPolynomialChart.Construction

noncomputable section

/-! The polynomial coordinates of a shifted negative twist have the canonical chart coefficient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem negativeTwistPolynomialSectionEquiv_chartCoefficient (j : σ) (a n : ℕ) (ha : a ≤ n)
    (x : (AlgebraicGeometry.SheafCohomology.Projective.AdditiveCoproductSections.baseGlobalSectionsFunctor (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      ((AlgebraicGeometry.SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.obj
        (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a))) :
    ProjectiveChartPolynomialMap.Construction.projectiveChartPolynomialMap j (AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistPolynomialSectionEquiv j a n ha x).val =
    AlgebraicGeometry.SheafCohomology.Projective.FrameSections.overTrivializationCoefficient (AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (n - a))
      (AlgebraicGeometry.SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.coordinateOpen j) (AlgebraicGeometry.SheafCohomology.Projective.PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSheafPowerOverFrame j j (n - a))
      ((AlgebraicGeometry.SheafCohomology.Projective.TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j a n ha).hom.val.app
        (.op ⊤) x) := by
  rw [AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistPolynomialSectionEquiv_apply]
  exact ProjectiveChartPolynomialMap.Construction.projectiveChartPolynomialMap_section j (n - a) _

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.NegativeTwistPolynomialChart.Construction
