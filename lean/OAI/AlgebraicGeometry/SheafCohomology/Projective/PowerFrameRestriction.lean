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

/-! # Power Frame Restriction -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PowerFrameRestriction.MvPolynomial

noncomputable section

open _root_.MvPolynomial

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
local instance twistFrameRestrictionMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

/-- Induced nonnegative-twist frames commute with restriction to a smaller
open. -/
theorem coordinateHyperplanePoleSheafPowerTrivializationOf_restrictOpen
    {U V : (Proj (homogeneousSubmodule σ R)).Opens} (hVU : V ≤ U) (j : σ)
    (e : (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j).restrict U.ι ≅
      Invertible.Scheme.Modules.unitObj U.toScheme) : ∀ n : ℕ,
    OpenFrames.Scheme.Modules.restrictOpenTrivialization hVU
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivializationOf U j e n) =
      TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivializationOf V j
        (OpenFrames.Scheme.Modules.restrictOpenTrivialization hVU e) n := by
  intro n
  induction n with
  | zero =>
      exact TensorFrameRestriction.restrictMonoidalUnitTrivialization_restrictOpen hVU
  | succ n ih =>
      simp only [TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivializationOf,
        TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower]
      rw [TensorFrameRestriction.restrictMonoidalTensorTrivialization_restrictOpen]
      rw [ih]

/-- Induced nonnegative `O(-1)`-power frames commute with restriction to a
smaller open. -/
theorem coordinateHyperplaneIdealModulePowerTrivializationOf_restrictOpen
    {U V : (Proj (homogeneousSubmodule σ R)).Opens} (hVU : V ≤ U) (j : σ)
    (e : (IdealModule.idealModule
        (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)).restrict U.ι ≅
      Invertible.Scheme.Modules.unitObj U.toScheme) : ∀ n : ℕ,
    OpenFrames.Scheme.Modules.restrictOpenTrivialization hVU
        (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivializationOf U j e n) =
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivializationOf V j
        (OpenFrames.Scheme.Modules.restrictOpenTrivialization hVU e) n := by
  intro n
  induction n with
  | zero =>
      exact TensorFrameRestriction.restrictMonoidalUnitTrivialization_restrictOpen hVU
  | succ n ih =>
      simp only [TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivializationOf,
        TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower]
      rw [TensorFrameRestriction.restrictMonoidalTensorTrivialization_restrictOpen]
      rw [ih]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PowerFrameRestriction.MvPolynomial
