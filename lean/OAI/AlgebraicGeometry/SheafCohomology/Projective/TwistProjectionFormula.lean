/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPullbackEquivalence
import OAI.AlgebraicGeometry.SheafCohomology.Projective.EquivalenceRightAdjointMate

/-! # Twist Projection Formula -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistProjectionFormula.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-!
# Pushforward projection formula for projective-space twists

The inverse-equivalence mate of negative-twist pullback compatibility gives
the positive-twist projection formula for pushforward along an arbitrary
morphism into polynomial projective space.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousIdeal MonoidalCategory

universe u

variable {R : Type u} {σ : Type} [CommRing R]
variable {X : Scheme.{u}}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Positive coordinate twists satisfy the projection formula for
pushforward along every morphism into polynomial projective space. -/
noncomputable def coordinateHyperplanePoleSheafPowerPushforwardTensorIso
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (n : ℕ) :
    let Pj := Proj (homogeneousSubmodule σ R)
    letI := Monoidal.Scheme.Modules.monoidalCategory Pj
    letI := Monoidal.Scheme.Modules.monoidalCategory X
    Scheme.Modules.pushforward f ⋙
        tensorRight (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n) ≅
      tensorRight ((Scheme.Modules.pullback f).obj
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)) ⋙
        Scheme.Modules.pushforward f := by
  let Pj := Proj (homogeneousSubmodule σ R)
  letI : MonoidalCategory Pj.Modules :=
    Monoidal.Scheme.Modules.monoidalCategory Pj
  letI : MonoidalCategory X.Modules :=
    Monoidal.Scheme.Modules.monoidalCategory X
  let E := PairedTwistEquivalence.MvPolynomial.coordinateHyperplaneTwistPairEquivalence
    (R := R) j n
  let EX := TwistPullbackEquivalence.MvPolynomial.pullbackCoordinateHyperplanePoleSheafPowerTensorEquivalence
    f j n
  let h := TwistPullbackEquivalence.MvPolynomial.coordinateHyperplaneIdealModulePowerTensorEquivalenceCompPullbackIso
    f j n
  exact EquivalenceRightAdjointMate.inverseEquivalenceCommutesWithRightAdjoint
    E.symm EX.symm
    (Scheme.Modules.pullback f) (Scheme.Modules.pushforward f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) h

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistProjectionFormula.MvPolynomial
