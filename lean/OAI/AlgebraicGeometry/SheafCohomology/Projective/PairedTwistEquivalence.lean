/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistShiftIso

/-! # Paired Twist Equivalence -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PairedTwistEquivalence.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-!
# Tensor equivalences from projective-space twists

Tensoring by the concrete positive coordinate-hyperplane twist `O(n)` is an
equivalence, with quasi-inverse given by tensoring by `O(-n)`.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousIdeal MonoidalCategory

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Tensoring by `O(n)` on polynomial projective space is an equivalence. -/
noncomputable def coordinateHyperplaneTwistPairEquivalence
    (j : σ) (n : ℕ) :
    let X := Proj (homogeneousSubmodule σ R)
    X.Modules ≌ X.Modules := by
  let X := Proj (homogeneousSubmodule σ R)
  letI : MonoidalCategory X.Modules :=
    Monoidal.Scheme.Modules.monoidalCategory X
  letI : SymmetricCategory X.Modules :=
    Monoidal.Scheme.Modules.symmetricCategory X
  let N := TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n
  let P := TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n
  let eNP : N ⊗ P ≅ 𝟙_ X.Modules :=
    TwistShiftIso.MvPolynomial.coordinateHyperplanePowerCancellationIso (R := R) j n
  let ePN : P ⊗ N ≅ 𝟙_ X.Modules :=
    (β_ P N) ≪≫ eNP
  let F := tensorRight P
  let G := tensorRight N
  let eta : 𝟭 X.Modules ≅ F ⋙ G :=
    (rightUnitorNatIso X.Modules).symm ≪≫
      (tensoringRight X.Modules).mapIso ePN.symm ≪≫
      tensorRightTensor P N
  let epsilon : G ⋙ F ≅ 𝟭 X.Modules :=
    (tensorRightTensor N P).symm ≪≫
      (tensoringRight X.Modules).mapIso eNP ≪≫
      rightUnitorNatIso X.Modules
  exact CategoryTheory.Equivalence.mk F G eta epsilon

/-- The functor underlying the positive-twist equivalence is right tensoring
by the concrete module `O(n)`. -/
@[simp]
theorem coordinateHyperplaneTwistPairEquivalence_functor
    (j : σ) (n : ℕ) :
    let X := Proj (homogeneousSubmodule σ R)
    letI := Monoidal.Scheme.Modules.monoidalCategory X
    (coordinateHyperplaneTwistPairEquivalence
      (R := R) j n).functor =
      tensorRight (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n) := by
  rfl

/-- The inverse functor of the positive-twist equivalence is right tensoring
by the concrete module `O(-n)`. -/
@[simp]
theorem coordinateHyperplaneTwistPairEquivalence_inverse
    (j : σ) (n : ℕ) :
    let X := Proj (homogeneousSubmodule σ R)
    letI := Monoidal.Scheme.Modules.monoidalCategory X
    (coordinateHyperplaneTwistPairEquivalence
      (R := R) j n).inverse =
      tensorRight (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n) := by
  rfl

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PairedTwistEquivalence.MvPolynomial
