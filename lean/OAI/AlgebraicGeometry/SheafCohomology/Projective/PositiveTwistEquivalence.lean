/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorExact
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorCoherent
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers

/-! # Positive Twist Equivalence -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-! Exact tensor equivalences for the actual positive projective twists. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance projectivePositiveTwistEquivalenceMonoidal
    (X : Scheme.{u}) : MonoidalCategory X.Modules := Monoidal.Scheme.Modules.monoidalCategory X

def coordinateHyperplanePoleSheafPowerTensorEquivalence (j : σ) (n : ℕ) :
    (Proj (homogeneousSubmodule σ R)).Modules ≌
      (Proj (homogeneousSubmodule σ R)).Modules :=
  InvertibleTensorEquivalence.invertibleRightTensorEquivalence
    (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
    (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower_isInvertible j n)

theorem moduleTensorCoordinateHyperplanePoleSheafPower_isQuasicoherent
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent]
    (j : σ) (n : ℕ) :
    (M ⊗ TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n).IsQuasicoherent :=
  (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower_isInvertible j n).tensorObj_isQuasicoherent

theorem moduleTensorCoordinateHyperplanePoleSheafPower_isFiniteType
    (M : (Proj (homogeneousSubmodule σ R)).Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (j : σ) (n : ℕ) :
    (M ⊗ TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n).IsFiniteType :=
  (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower_isInvertible j n).tensorObj_isFiniteType

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PositiveTwistEquivalence.MvPolynomial
