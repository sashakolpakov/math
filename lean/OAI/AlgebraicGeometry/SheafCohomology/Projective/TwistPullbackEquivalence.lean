/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PairedTwistEquivalence
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PullbackTensorMonoidal

/-! # Twist Pullback Equivalence -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPullbackEquivalence.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-!
# Pullback equivalences from projective-space twists

The concrete equivalence given by tensoring with `O(n)` pulls back along an
arbitrary morphism to polynomial projective space. Its inverse is tensoring
with the pullback of `O(-n)`.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousIdeal MonoidalCategory

universe u

variable {R : Type u} {σ : Type} [CommRing R]
variable {X : Scheme.{u}}

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Tensoring by the pullback of `O(n)` is an equivalence, with inverse
given by tensoring by the pullback of `O(-n)`. -/
noncomputable def pullbackCoordinateHyperplanePoleSheafPowerTensorEquivalence
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (n : ℕ) :
    X.Modules ≌ X.Modules := by
  let Pj := Proj (homogeneousSubmodule σ R)
  letI : MonoidalCategory Pj.Modules :=
    Projective.Monoidal.Scheme.Modules.monoidalCategory Pj
  letI : SymmetricCategory Pj.Modules :=
    Projective.Monoidal.Scheme.Modules.symmetricCategory Pj
  letI : MonoidalCategory X.Modules :=
    Projective.Monoidal.Scheme.Modules.monoidalCategory X
  letI : SymmetricCategory X.Modules :=
    Projective.Monoidal.Scheme.Modules.symmetricCategory X
  letI : (Scheme.Modules.pullback f).Monoidal :=
    PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f
  let N := TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n
  let P := TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n
  let eNP : N ⊗ P ≅ 𝟙_ Pj.Modules :=
    TwistShiftIso.MvPolynomial.coordinateHyperplanePowerCancellationIso (R := R) j n
  let ePbNP :
      (Scheme.Modules.pullback f).obj N ⊗
          (Scheme.Modules.pullback f).obj P ≅ 𝟙_ X.Modules :=
    Functor.Monoidal.μIso (Scheme.Modules.pullback f) N P ≪≫
      (Scheme.Modules.pullback f).mapIso eNP ≪≫
      (Functor.Monoidal.εIso (Scheme.Modules.pullback f)).symm
  let ePbPN :
      (Scheme.Modules.pullback f).obj P ⊗
          (Scheme.Modules.pullback f).obj N ≅ 𝟙_ X.Modules :=
    (β_ _ _) ≪≫ ePbNP
  let F := tensorRight ((Scheme.Modules.pullback f).obj P)
  let G := tensorRight ((Scheme.Modules.pullback f).obj N)
  let eta : 𝟭 X.Modules ≅ F ⋙ G :=
    (rightUnitorNatIso X.Modules).symm ≪≫
      (tensoringRight X.Modules).mapIso ePbPN.symm ≪≫
      tensorRightTensor _ _
  let epsilon : G ⋙ F ≅ 𝟭 X.Modules :=
    (tensorRightTensor _ _).symm ≪≫
      (tensoringRight X.Modules).mapIso ePbNP ≪≫
      rightUnitorNatIso X.Modules
  exact CategoryTheory.Equivalence.mk F G eta epsilon

/-- The functor of the pulled-back positive-twist equivalence is right
tensoring by the pullback of `O(n)`. -/
@[simp]
theorem pullbackCoordinateHyperplanePoleSheafPowerTensorEquivalence_functor
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (n : ℕ) :
    letI := Projective.Monoidal.Scheme.Modules.monoidalCategory X
    (pullbackCoordinateHyperplanePoleSheafPowerTensorEquivalence f j n).functor =
      tensorRight ((Scheme.Modules.pullback f).obj
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)) := by
  rfl

/-- The inverse functor of the pulled-back positive-twist equivalence is
right tensoring by the pullback of `O(-n)`. -/
@[simp]
theorem pullbackCoordinateHyperplanePoleSheafPowerTensorEquivalence_inverse
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (n : ℕ) :
    letI := Projective.Monoidal.Scheme.Modules.monoidalCategory X
    (pullbackCoordinateHyperplanePoleSheafPowerTensorEquivalence f j n).inverse =
      tensorRight ((Scheme.Modules.pullback f).obj
        (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n)) := by
  rfl

/-- Negative projective twists commute with pullback. This is the
left-adjoint comparison whose mate gives the positive-twist projection
formula for pushforward. -/
noncomputable def coordinateHyperplaneIdealModulePowerTensorEquivalenceCompPullbackIso
    (f : X ⟶ Proj (homogeneousSubmodule σ R)) (j : σ) (n : ℕ) :
    let Pj := Proj (homogeneousSubmodule σ R)
    letI := Projective.Monoidal.Scheme.Modules.monoidalCategory Pj
    letI := Projective.Monoidal.Scheme.Modules.monoidalCategory X
    (PairedTwistEquivalence.MvPolynomial.coordinateHyperplaneTwistPairEquivalence
        (R := R) j n).inverse ⋙ Scheme.Modules.pullback f ≅
      Scheme.Modules.pullback f ⋙
        (pullbackCoordinateHyperplanePoleSheafPowerTensorEquivalence
          f j n).inverse := by
  let Pj := Proj (homogeneousSubmodule σ R)
  letI : MonoidalCategory Pj.Modules :=
    Projective.Monoidal.Scheme.Modules.monoidalCategory Pj
  letI : MonoidalCategory X.Modules :=
    Projective.Monoidal.Scheme.Modules.monoidalCategory X
  letI : (Scheme.Modules.pullback f).Monoidal :=
    PullbackTensorGeneral.Scheme.Modules.pullbackMonoidal f
  rw [PairedTwistEquivalence.MvPolynomial.coordinateHyperplaneTwistPairEquivalence_inverse,
    pullbackCoordinateHyperplanePoleSheafPowerTensorEquivalence_inverse]
  exact (Functor.Monoidal.commTensorRight
    (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n)
    (F := Scheme.Modules.pullback f)).symm

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPullbackEquivalence.MvPolynomial
