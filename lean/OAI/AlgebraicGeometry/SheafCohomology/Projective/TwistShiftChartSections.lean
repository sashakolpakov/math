import OAI.AlgebraicGeometry.SheafCohomology.Projective.DistinguishedChartCancellation
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PositivePowerSectionAddition
import OAI.AlgebraicGeometry.SheafCohomology.Projective.RestrictedUnitTensorSection
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorCancellationShiftSections

/-! # Twist Shift Chart Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistShiftChartSections

noncomputable section

open _root_.MvPolynomial

/-! Projective degree shifts preserve the normalized sections on the distinguished chart. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
local instance twistShiftChartMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

theorem coordinateHyperplaneTwistShiftAdd_eq_tensorCancellation (j : σ) (m n : ℕ) :
    TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerAddIso (R := R) j m n =
      TensorCancellationShiftSections.tensorCancellationShiftIso
        (TwistShiftIso.MvPolynomial.coordinateHyperplanePoleSheafPower_addIso (R := R) j m n)
        (TwistShiftIso.MvPolynomial.coordinateHyperplanePowerCancellationIso (R := R) j m) := rfl

theorem coordinateHyperplanePoleSheafPower_addIso_restrict_section (j : σ) (m n : ℕ)
    (U : (Proj (homogeneousSubmodule σ R)).Opens) :
    (TwistShiftIso.MvPolynomial.coordinateHyperplanePoleSheafPower_addIso (R := R) j m n).hom.val.app (op U)
      ((TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (m + n)).presheaf.map
        (homOfLE (le_top : U ≤ ⊤)).op (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j (m + n))) =
      TensorSections.tensorSection _ _ U
        ((TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m).presheaf.map
          (homOfLE (le_top : U ≤ ⊤)).op (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j m))
        ((TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n).presheaf.map
          (homOfLE (le_top : U ≤ ⊤)).op (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j n)) := by
  have h := PresheafOfModules.naturality_apply
    (TwistShiftIso.MvPolynomial.coordinateHyperplanePoleSheafPower_addIso (R := R) j m n).hom.val
    (homOfLE (le_top : U ≤ ⊤)).op (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j (m + n))
  rw [PositivePowerSectionAddition.MvPolynomial.coordinateHyperplanePoleSheafPower_addIso_section, TensorSections.tensorSection_restrict] at h
  exact h

theorem coordinateHyperplaneTwistShiftAdd_chart_section (j : σ) (m n : ℕ) :
    (TwistShiftIso.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerAddIso (R := R) j m n).hom.val.app
      (op (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
      (TensorSections.tensorSection _ _ (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
        (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j m)
        ((TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (m + n)).presheaf.map
          (homOfLE le_top).op (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j (m + n)))) =
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n).presheaf.map
        (homOfLE (le_top : MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j ≤ ⊤)).op
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j n) := by
  rw [coordinateHyperplaneTwistShiftAdd_eq_tensorCancellation]
  let U := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
  have h := TensorCancellationShiftSections.tensorCancellationShiftIso_tensorSection
    (TwistShiftIso.MvPolynomial.coordinateHyperplanePoleSheafPower_addIso (R := R) j m n)
    (TwistShiftIso.MvPolynomial.coordinateHyperplanePowerCancellationIso (R := R) j m) U
    (DistinguishedChartCancellation.MvPolynomial.coordinateHyperplaneIdealChartPowerSection (R := R) j m)
    ((TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j m))
    ((TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j n))
    ((TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (m + n)).presheaf.map
      (homOfLE (le_top : U ≤ ⊤)).op (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j (m + n)))
    (coordinateHyperplanePoleSheafPower_addIso_restrict_section j m n U)
  rw [DistinguishedChartCancellation.MvPolynomial.coordinateHyperplanePowerCancellationIso_chart_section,
    RestrictedUnitTensorSection.leftUnitor_tensorSection_restrict] at h
  exact h

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistShiftChartSections
