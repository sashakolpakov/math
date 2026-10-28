import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistShiftChartSections

/-! # Of LE Chart Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.OfLEChartSections

noncomputable section

open _root_.MvPolynomial

/-! Normalized projective degree shifts under a degree inequality. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
local instance twistShiftOfLEChartMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

theorem coordinateHyperplaneTwistShift_chart_section_of_eq
    (j : σ) (m n k : ℕ) (h : n = m + k) :
    ((eqToIso (congrArg (fun t => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j m ⊗
      TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j t) h) ≪≫
        TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerAddIso (R := R) j m k).hom.val.app
      (op (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)))
      (TensorSections.tensorSection _ _ (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
        (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j m)
        ((TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n).presheaf.map
          (homOfLE le_top).op (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j n))) =
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j k).presheaf.map
        (homOfLE (le_top : MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j ≤ ⊤)).op
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j k) := by
  subst n
  simpa only [eqToIso_refl, Iso.refl_trans] using
    TwistShiftChartSections.MvPolynomial.coordinateHyperplaneTwistShiftAdd_chart_section (R := R) j m k

theorem coordinateHyperplaneTwistShiftOfLE_chart_section (j : σ) (m n : ℕ) (hmn : m ≤ n) :
    (TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE (R := R) j m n hmn).hom.val.app
      (op (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
      (TensorSections.tensorSection _ _ (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
        (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j m)
        ((TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n).presheaf.map
          (homOfLE le_top).op (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j n))) =
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (n - m)).presheaf.map
        (homOfLE (le_top : MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j ≤ ⊤)).op
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j (n - m)) := by
  exact coordinateHyperplaneTwistShift_chart_section_of_eq (R := R) j m n (n - m)
    (Nat.add_sub_of_le hmn).symm

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.OfLEChartSections
