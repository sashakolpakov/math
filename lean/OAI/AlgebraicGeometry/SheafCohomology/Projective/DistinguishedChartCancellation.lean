import OAI.AlgebraicGeometry.SheafCohomology.Projective.LocalPowerSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PositivePowerChartGenerator

/-! # Distinguished Chart Cancellation -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.DistinguishedChartCancellation

noncomputable section

open _root_.MvPolynomial

/-! Cancellation of the canonical positive section against its local inverse powers. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite
universe u
namespace MvPolynomial
open OAI.AlgebraicGeometry.SheafCohomology.Projective.PositivePowerChartGenerator
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
local instance distinguishedCancellationMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

theorem coordinateHyperplanePoleSection_overCoefficient_self (j : σ) :
    FrameSections.overTrivializationCoefficient (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j)
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) (HyperplaneLocalSection.MvPolynomial.coordinateHyperplanePoleOverTrivialization (R := R) j j)
      (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSection (R := R) j) = 1 := by
  rw [FrameSectionComparison.overTrivializationCoefficient_eq_local_of_overIso _
    ⟨MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j, MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen j⟩]
  unfold FrameSections.localTrivializationCoefficient
  rw [HyperplaneLocalSection.MvPolynomial.coordinateHyperplanePoleSection_coefficient_over, CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_self]
  simp only [FrameSections.affineOpenTopSection, map_one, FrameSections.affineOpenAmbientSection]

def coordinateHyperplaneIdealChartPowerSection (j : σ) (n : ℕ) :
    Γ(TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n, MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) :=
  LocalPowerSections.MvPolynomial.coordinateHyperplaneIdealLocalTensorPower j (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
    (FrameSections.overTrivializationSection (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) (HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization (R := R) j j) 1) n

theorem coordinateHyperplanePowerPairing_chart_one (j : σ) (n : ℕ) :
    (PowerCancellationPairing.MvPolynomial.coordinateHyperplanePowerPairing (R := R) j n).val.app (op (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
      (TensorSections.tensorSection _ _ (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
        (coordinateHyperplaneIdealChartPowerSection (R := R) j n)
        ((TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n).presheaf.map
          (homOfLE le_top).op (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j n))) =
      (show Γ(Proj (homogeneousSubmodule σ R), MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) from 1) := by
  let U := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j
  let I := IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)
  let P := HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j
  let e := HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization (R := R) j j
  let d := HyperplaneLocalSection.MvPolynomial.coordinateHyperplanePoleOverTrivialization (R := R) j j
  let y := P.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
    (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSection (R := R) j)
  have hy : y = FrameSections.overTrivializationSection P U d 1 := by
    have hc := coordinateHyperplanePoleSection_overCoefficient_self (R := R) j
    have hi := (RankOneMapCoordinates.overFrameSectionEquiv P U d).apply_symm_apply y
    change FrameSections.overTrivializationSection P U d
      (FrameSections.overTrivializationCoefficient P U d (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSection (R := R) j)) = y at hi
    rw [hc] at hi
    exact hi.symm
  have heval : (TensorFrameSections.dualPairing I).val.app (op U)
      (TensorSections.tensorSection I P U (FrameSections.overTrivializationSection I U e 1) y) =
        (show Γ(Proj (homogeneousSubmodule σ R), U) from 1) := by
    rw [hy]
    exact TensorFrameSections.dualPairing_overTrivializationSection_one I U e
  rw [← LocalPowerSections.MvPolynomial.coordinateHyperplanePoleLocalTensorPower_restrict]
  change (PowerCancellationPairing.MvPolynomial.coordinateHyperplanePowerPairing j n).val.app (op U)
    (TensorSections.tensorSection _ _ U (LocalPowerSections.MvPolynomial.coordinateHyperplaneIdealLocalTensorPower j U
      (FrameSections.overTrivializationSection I U e 1) n) (LocalPowerSections.MvPolynomial.coordinateHyperplanePoleLocalTensorPower j U y n)) = _
  rw [LocalPowerSections.MvPolynomial.coordinateHyperplanePowerPairing_localTensorPowers]
  erw [heval, one_pow]

theorem coordinateHyperplanePowerCancellationIso_chart_section (j : σ) (n : ℕ) :
    (TwistShiftIso.MvPolynomial.coordinateHyperplanePowerCancellationIso (R := R) j n).hom.val.app
      (op (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
      (TensorSections.tensorSection _ _ (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
        (coordinateHyperplaneIdealChartPowerSection (R := R) j n)
        ((TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n).presheaf.map
          (homOfLE le_top).op (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j n))) =
      PowerCancellationPairing.localMonoidalUnitSection (Proj (homogeneousSubmodule σ R)) (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) := by
  let c := TensorSections.monoidalUnitObjIso (Proj (homogeneousSubmodule σ R))
  have h := congrArg (fun r => c.inv.val.app (op (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)) r)
    (coordinateHyperplanePowerPairing_chart_one (R := R) j n)
  change c.inv.val.app _ (c.hom.val.app _ _) = _ at h
  erw [SectionIdentities.Scheme.Modules.iso_inv_hom_app_applyT c.symm] at h
  exact h

theorem coordinateHyperplaneCancellationUnitIso_chart_inverse (j : σ) (n : ℕ) :
    (TwistShiftIso.MvPolynomial.coordinateHyperplanePowerCancellationIso (R := R) j n ≪≫
      TensorSections.monoidalUnitObjIso (Proj (homogeneousSubmodule σ R))).inv.val.app
      (op (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
      (show Γ(Proj (homogeneousSubmodule σ R), MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j) from 1) =
      TensorSections.tensorSection _ _ (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)
        (coordinateHyperplaneIdealChartPowerSection (R := R) j n)
        ((TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n).presheaf.map
          (homOfLE le_top).op (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j n)) := by
  let e := TwistShiftIso.MvPolynomial.coordinateHyperplanePowerCancellationIso (R := R) j n ≪≫
    TensorSections.monoidalUnitObjIso (Proj (homogeneousSubmodule σ R))
  have h := congrArg (fun r => e.inv.val.app (op (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j)) r)
    (coordinateHyperplanePowerPairing_chart_one (R := R) j n)
  change e.inv.val.app _ (e.hom.val.app _ _) = _ at h
  exact h.symm.trans (SectionIdentities.Scheme.Modules.iso_inv_hom_app_applyT e.symm _ _)

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.DistinguishedChartCancellation
