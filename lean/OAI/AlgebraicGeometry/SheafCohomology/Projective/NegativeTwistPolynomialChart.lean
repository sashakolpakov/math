import OAI.AlgebraicGeometry.SheafCohomology.Projective.ChartPolynomialMap
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistedCoproductPolynomialSections

/-! # Negative Twist Polynomial Chart -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistPolynomialChart.Dimension

noncomputable section

/-! The polynomial coordinates of a shifted negative twist have the canonical chart coefficient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem negativeTwistPolynomialSectionEquiv_chartCoefficient (j : σ) (a n : ℕ) (ha : a ≤ n)
    (x : (AdditiveCoproductSections.baseGlobalSectionsFunctor (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))).obj
      ((PositiveTwistEquivalence.MvPolynomial.coordinateHyperplanePoleSheafPowerTensorEquivalence (R := R) j n).functor.obj
        (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a))) :
    ChartPolynomialMap.Dimension.projectiveChartPolynomialMap j (TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistPolynomialSectionEquiv j a n ha x).val =
    FrameSections.overTrivializationCoefficient (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (n - a))
      (MvPolynomialClosure.MvPolynomial.coordinateOpen j) (PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSheafPowerOverFrame j j (n - a))
      ((TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j a n ha).hom.val.app
        (.op ⊤) x) := by
  rw [TwistedCoproductPolynomialSections.MvPolynomial.negativeTwistPolynomialSectionEquiv_apply]
  exact ChartPolynomialMap.Dimension.projectiveChartPolynomialMap_section j (n - a) _

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistPolynomialChart.Dimension
