import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeChartCoordinates
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OfLEChartSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialSectionProductCriterion

/-! # Negative Twist Hom Chart -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomChart

noncomputable section

open _root_.MvPolynomial

/-! The positive section encoding a negative-twist map has the map's normalized chart coefficient. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
local instance negativeHomChartMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

def coordinateNegativeTwistMapChartCoefficient (j : σ) (a b : ℕ)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) :
    Γ(Proj (homogeneousSubmodule σ R), MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) :=
  NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneNegativeChartCoefficient j b
    (f.val.app (op (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
      (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j a))

theorem coordinateNegativeTwistHomSection_chartCoefficient (j : σ) (a b : ℕ) (hba : b ≤ a)
    (f : TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j a ⟶
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j b) :
    PolynomialSectionProductCriterion.MvPolynomial.coordinateTwistChartCoefficient (R := R) j j (a - b)
      (NegativeTwistHomSections.MvPolynomial.coordinateNegativeTwistHomSection (R := R) j a b hba f) =
      coordinateNegativeTwistMapChartCoefficient j a b f := by
  let U := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
  let P := TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (a - b)
  let q := RankOneMapCoordinates.overFrameSectionEquiv P U (PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSheafPowerOverFrame (R := R) j j (a - b))
  have hr := HomSectionEquivEvaluation.unitHomTopSection_restrict P (NegativeTwistHomSections.MvPolynomial.coordinateNegativeTwistHomUnitMap j a b hba f) U
  change P.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
    (NegativeTwistHomSections.MvPolynomial.coordinateNegativeTwistHomSection j a b hba f) =
      (NegativeTwistHomSections.MvPolynomial.coordinateNegativeTwistHomUnitMap j a b hba f).val.app (op U)
        (show Γ(Proj (homogeneousSubmodule σ R), U) from 1) at hr
  conv_rhs at hr => rw [NegativeTwistHomSections.MvPolynomial.coordinateNegativeTwistHomUnitMap_eq_tensor]
  change P.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
    (NegativeTwistHomSections.MvPolynomial.coordinateNegativeTwistHomSection j a b hba f) =
      (TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j b a hba).hom.val.app
        (op U) ((f ⊗ₘ 𝟙 (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j a)).val.app (op U)
          ((TwistShiftIso.MvPolynomial.coordinateHyperplanePowerCancellationIso (R := R) j a ≪≫ TensorSections.monoidalUnitObjIso _).inv.val.app
            (op U) (show Γ(Proj (homogeneousSubmodule σ R), U) from 1))) at hr
  rw [DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneCancellationUnitIso_chart_inverse, TensorFrameSections.tensorSection_map] at hr
  change P.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
    (NegativeTwistHomSections.MvPolynomial.coordinateNegativeTwistHomSection j a b hba f) =
      (TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j b a hba).hom.val.app
        (op U) (TensorSections.tensorSection _ _ U
          (f.val.app (op U) (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j a))
          ((TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j a).presheaf.map
            (homOfLE (le_top : U ≤ ⊤)).op (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j a))) at hr
  rw [NegativeChartCoordinates.MvPolynomial.coordinateHyperplaneIdealChartPowerSection_generates j b
    (f.val.app (op U) (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j a)),
    TensorSectionBilinear.tensorSection_smul_left, map_smul, OfLEChartSections.MvPolynomial.coordinateHyperplaneTwistShiftOfLE_chart_section] at hr
  change q.symm (P.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
    (NegativeTwistHomSections.MvPolynomial.coordinateNegativeTwistHomSection j a b hba f)) = _
  rw [hr, q.symm.map_smul]
  change coordinateNegativeTwistMapChartCoefficient j a b f *
    FrameSections.overTrivializationCoefficient P U (PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSheafPowerOverFrame (R := R) j j (a - b))
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j (a - b)) = _
  rw [PositivePowerChartGenerator.MvPolynomial.coordinateHyperplanePoleSectionPower_coefficient_self, mul_one]

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistHomChart
