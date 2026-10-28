import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistShiftedMapSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FramedMapGeneratorCoefficient
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialSectionProductDegree

/-! # Negative Twist Shifted Map -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistShiftedMap

noncomputable section

open _root_.MvPolynomial

/-! Twisting an actual map between negative twists acts by its homogeneous polynomial. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite OAI.AlgebraicGeometry.SheafCohomology.Projective.FramedMapGeneratorCoefficient
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
local instance negativeShiftedPolynomialMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

theorem coordinateNegativeTwistShiftedMap_chart_coefficient
    (j : σ) (a b N : ℕ) (ha : a ≤ N) (hb : b ≤ N)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b)
    (x : Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (N - a), ⊤)) :
    PolynomialSectionProductCriterion.MvPolynomial.coordinateTwistChartCoefficient j j (N - b)
        ((TwistShiftedMapSections.MvPolynomial.coordinateNegativeTwistShiftedMap j a b N ha hb f).val.app (op ⊤) x) =
      NegativeTwistHomChart.MvPolynomial.coordinateNegativeTwistMapChartCoefficient j a b f *
        PolynomialSectionProductCriterion.MvPolynomial.coordinateTwistChartCoefficient j j (N - a) x := by
  have hg := TwistShiftedMapSections.MvPolynomial.coordinateNegativeTwistShiftedMap_chart_generator (R := R) j a b N ha hb f
  refine FramedMapGeneratorCoefficient.overFrameMap_globalCoefficient_of_generator
    (X := Proj (homogeneousSubmodule σ R))
    (M := TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (N - a))
    (N := TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (N - b))
    (TwistShiftedMapSections.MvPolynomial.coordinateNegativeTwistShiftedMap (R := R) j a b N ha hb f) (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
    (PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSheafPowerOverFrame (R := R) j j (N - a))
    (PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSheafPowerOverFrame (R := R) j j (N - b))
    (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j (N - a))
    (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j (N - b))
    (NegativeTwistHomChart.MvPolynomial.coordinateNegativeTwistMapChartCoefficient j a b f)
    (PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSectionPower_coefficient_self (R := R) j (N - a))
    (PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSectionPower_coefficient_self (R := R) j (N - b))
    ?_ x
  set_option backward.dsimp.proofs true in
    dsimp +instances only [Scheme.Opens, SheafedSpace.instTopologicalSpaceCarrierCarrier] at hg ⊢
  exact hg

theorem coordinateNegativeTwistShiftedMap_polynomial [Fintype σ] [LinearOrder σ]
    (j : σ) (a b N : ℕ) (hba : b ≤ a) (ha : a ≤ N) (hb : b ≤ N)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b)
    (x : Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (N - a), ⊤)) :
    (DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j (N - b)
      ((TwistShiftedMapSections.MvPolynomial.coordinateNegativeTwistShiftedMap j a b N ha hb f).val.app (op ⊤) x)).val =
      (NegativeTwistHomPolynomials.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials (R := R) j a b hba f).val *
        (DegreeZeroPolynomials.MvPolynomial.coordinateTwistGlobalSectionsLinearEquivPolynomials (R := R) j (N - a) x).val := by
  rw [NegativeTwistHomSections.MvPolynomial.coordinateNegativeTwistHomEquivPolynomials_apply]
  apply PolynomialSectionProductDegree.MvPolynomial.coordinateTwistPolynomial_eq_mul_of_coefficient_of_degree j j
    (a - b) (N - a) (N - b) (by omega)
    (NegativeTwistHomSections.MvPolynomial.coordinateNegativeTwistHomSection (R := R) j a b hba f) x
  rw [coordinateNegativeTwistShiftedMap_chart_coefficient,
    NegativeTwistHomChart.MvPolynomial.coordinateNegativeTwistHomSection_chartCoefficient]

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistShiftedMap
