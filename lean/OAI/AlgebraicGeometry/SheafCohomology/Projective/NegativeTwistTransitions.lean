/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorFrameRestriction
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneTransitions
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistFrameScalar
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FrameTransitionTransport
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PowerFrameRestriction

/-! # Negative Twist Transitions -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistTransitions.MvPolynomial

noncomputable section

open _root_.MvPolynomial

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
local instance negativeTwistTransitionMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

/-- On a coordinate overlap, the two `O(-n)` frames differ by the `n`th power
of `X_k / X_i`, in the orientation of the `O(-1)` generator frames. -/
theorem coordinateHyperplaneIdealModulePowerTrivialization_restrict_transition
    (i k j : σ) (n : ℕ) :
    (OpenFrames.Scheme.Modules.restrictOpenTrivialization
        (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)
        (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivialization
          (R := R) k j n)).hom =
      (OpenFrames.Scheme.Modules.restrictOpenTrivialization
          (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)
          (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivialization
            (R := R) i j n)).hom ≫
        UnitScalar.unitEndomorphismOfTopSection
          ((OpenFrames.Scheme.Modules.openTopSection
            (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)
            (CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k :
              Γ(Proj (homogeneousSubmodule σ R),
                CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k))) ^ n) := by
  let U := CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k
  let eI := OpenFrames.Scheme.Modules.restrictOpenTrivialization
    (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)
    (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm
  let eK := OpenFrames.Scheme.Modules.restrictOpenTrivialization
    (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)
    (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) k j).symm
  let r := OpenFrames.Scheme.Modules.openTopSection U
    (CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k :
      Γ(Proj (homogeneousSubmodule σ R), U))
  have hbase : eK.hom = eI.hom ≫
      UnitScalar.unitEndomorphismOfTopSection r := by
    exact HyperplaneTransitions.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization_restrict_transition i k j
  have hpower := PowerFrameScalar.recursiveTensorTrivialization_hom_eq_comp_scalar U
    (fun e n => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivializationOf U j e n)
    (fun n => TensorSections.restrictMonoidalTensorIso U.ι
      (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n)
      (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)))
    (fun _ _ => rfl) (fun _ _ => rfl) eK eI r hbase n
  have hI :
      OpenFrames.Scheme.Modules.restrictOpenTrivialization
          (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)
          (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivialization
            (R := R) i j n) =
        TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivializationOf U j eI n := by
    exact PowerFrameRestriction.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivializationOf_restrictOpen
      (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k) j
        (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm n
  have hK :
      OpenFrames.Scheme.Modules.restrictOpenTrivialization
          (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)
          (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivialization
            (R := R) k j n) =
        TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivializationOf U j eK n := by
    exact PowerFrameRestriction.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivializationOf_restrictOpen
      (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k) j
        (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) k j).symm n
  rw [hK, hI]
  exact hpower

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.NegativeTwistTransitions.MvPolynomial
