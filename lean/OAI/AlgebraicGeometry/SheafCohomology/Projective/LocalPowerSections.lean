import OAI.AlgebraicGeometry.SheafCohomology.Projective.PowerCancellationPairing
import OAI.AlgebraicGeometry.SheafCohomology.Projective.RestrictedUnitTensorSection

/-! # Local Power Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.LocalPowerSections

noncomputable section

open _root_.MvPolynomial

/-! Local tensor powers and their canonical cancellation pairing. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite
universe u
namespace MvPolynomial
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
local instance localPowerSectionsMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

def coordinateHyperplaneIdealLocalTensorPower (j : σ)
    (U : (Proj (homogeneousSubmodule σ R)).Opens)
    (x : Γ(IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j), U)) :
    (n : ℕ) → Γ(TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n, U)
  | 0 => PowerCancellationPairing.localMonoidalUnitSection _ U
  | n + 1 => TensorSections.tensorSection _ _ U (coordinateHyperplaneIdealLocalTensorPower j U x n) x

def coordinateHyperplanePoleLocalTensorPower (j : σ)
    (U : (Proj (homogeneousSubmodule σ R)).Opens)
    (y : Γ(HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j, U)) :
    (n : ℕ) → Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n, U)
  | 0 => PowerCancellationPairing.localMonoidalUnitSection _ U
  | n + 1 => TensorSections.tensorSection _ _ U (coordinateHyperplanePoleLocalTensorPower j U y n) y

theorem coordinateHyperplaneIdealLocalTensorPower_succ (j : σ)
    (U : (Proj (homogeneousSubmodule σ R)).Opens)
    (x : Γ(IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j), U)) (n : ℕ) :
    LocalPowerSections.MvPolynomial.coordinateHyperplaneIdealLocalTensorPower j U x (n + 1) =
      TensorSections.tensorSection (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n)
        (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)) U
        (LocalPowerSections.MvPolynomial.coordinateHyperplaneIdealLocalTensorPower j U x n) x := rfl

theorem coordinateHyperplanePoleLocalTensorPower_succ (j : σ)
    (U : (Proj (homogeneousSubmodule σ R)).Opens)
    (y : Γ(HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j, U)) (n : ℕ) :
    LocalPowerSections.MvPolynomial.coordinateHyperplanePoleLocalTensorPower j U y (n + 1) =
      TensorSections.tensorSection (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
        (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j) U
        (LocalPowerSections.MvPolynomial.coordinateHyperplanePoleLocalTensorPower j U y n) y := rfl

theorem coordinateHyperplanePowerPairing_localTensorPowers (j : σ)
    (U : (Proj (homogeneousSubmodule σ R)).Opens)
    (x : Γ(IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j), U))
    (y : Γ(HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j, U)) (n : ℕ) :
    (PowerCancellationPairing.MvPolynomial.coordinateHyperplanePowerPairing (R := R) j n).val.app (op U)
      (TensorSections.tensorSection _ _ U (LocalPowerSections.MvPolynomial.coordinateHyperplaneIdealLocalTensorPower j U x n)
        (LocalPowerSections.MvPolynomial.coordinateHyperplanePoleLocalTensorPower j U y n)) =
      (show Γ(Proj (homogeneousSubmodule σ R), U) from
        (TensorFrameSections.dualPairing (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))).val.app (op U)
          (TensorSections.tensorSection _ _ U x y)) ^ n := by
  induction n with
  | zero =>
      rw [PowerCancellationPairing.MvPolynomial.coordinateHyperplanePowerPairing_zero, pow_zero]
      exact PowerCancellationPairing.unitPairing_localMonoidalUnitSection _ U
  | succ n ih =>
      rw [coordinateHyperplaneIdealLocalTensorPower_succ,
        coordinateHyperplanePoleLocalTensorPower_succ, PowerCancellationPairing.MvPolynomial.coordinateHyperplanePowerPairing_succ]
      simp only [TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower_succ,
        TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower_succ]
      erw [TensorFrameSections.tensorPairing_tensorSection, ih, pow_succ]

theorem coordinateHyperplanePoleLocalTensorPower_restrict (j : σ)
    (U : (Proj (homogeneousSubmodule σ R)).Opens) (n : ℕ) :
    LocalPowerSections.MvPolynomial.coordinateHyperplanePoleLocalTensorPower j U
        ((HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j).presheaf.map
          (homOfLE le_top).op (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSection (R := R) j)) n =
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n).presheaf.map
        (homOfLE le_top).op (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j n) := by
  induction n with
  | zero =>
      exact RestrictedUnitTensorSection.localMonoidalUnitSection_eq_restrict _ U
  | succ n ih =>
      change TensorSections.tensorSection _ _ U _ _ = _
      rw [ih]
      exact (TensorSections.tensorSection_restrict (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
        (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j) (le_top : U ≤ ⊤)
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j n)
        (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSection (R := R) j)).symm

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.LocalPowerSections
