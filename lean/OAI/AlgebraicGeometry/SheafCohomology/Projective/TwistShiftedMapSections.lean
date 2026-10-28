import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomChart
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorConjugatedMapSections

/-! # Twist Shifted Map Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistShiftedMapSections

noncomputable section

open _root_.MvPolynomial

/-! Twisting an actual map between negative twists acts by its homogeneous polynomial. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorConjugatedMapSections
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
local instance negativeShiftedMapMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

def coordinateNegativeTwistShiftedMap (j : σ) (a b N : ℕ) (ha : a ≤ N) (hb : b ≤ N)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) :
    TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (N - a) ⟶
      TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (N - b) :=
  TensorConjugatedMapSections.tensorConjugatedMap
    (TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j a N ha)
    (TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j b N hb) f

theorem coordinateNegativeTwistShiftedMap_chart_generator
    (j : σ) (a b N : ℕ) (ha : a ≤ N) (hb : b ≤ N)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) :
    (coordinateNegativeTwistShiftedMap j a b N ha hb f).val.app (op (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
      ((TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (N - a)).presheaf.map
        (homOfLE le_top).op (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j (N - a))) =
      NegativeTwistHomChart.MvPolynomial.coordinateNegativeTwistMapChartCoefficient j a b f •
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (N - b)).presheaf.map
          (homOfLE (le_top : MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j ≤ ⊤)).op
          (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j (N - b)) := by
  exact TensorConjugatedMapSections.tensorConjugatedMap_section
    (TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j a N ha)
    (TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j b N hb) f
    (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
    (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j a)
    (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j b)
    ((TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j N).presheaf.map
      (homOfLE (le_top : MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j ≤ ⊤)).op
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j N))
    _ _ (NegativeTwistHomChart.MvPolynomial.coordinateNegativeTwistMapChartCoefficient j a b f)
    (OfLEChartSections.MvPolynomial.coordinateHyperplaneTwistShiftOfLE_chart_section (R := R) j a N ha)
    (OfLEChartSections.MvPolynomial.coordinateHyperplaneTwistShiftOfLE_chart_section (R := R) j b N hb)
    (NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneIdealChartPowerSection_generates (R := R) j b
      (f.val.app (op (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
        (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j a)))

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistShiftedMapSections
