/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorPowerCancellation
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleEvaluation
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleCancellationPairing

/-! # Twist Shift Iso -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistShiftIso.MvPolynomial

noncomputable section

open _root_.MvPolynomial

/-!
# Shift isomorphisms for projective-space twists

Positive powers of the coordinate-hyperplane twist are additive, and
tensoring `O(-m)` with `O(n)` for `m ≤ n` gives `O(n-m)`.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.HomogeneousIdeal MonoidalCategory

universe u

variable {R : Type u} {σ : Type} [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable local instance projectiveSpaceTwistShiftMonoidalCategory
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

noncomputable local instance projectiveSpaceTwistShiftSymmetricCategory
    (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Monoidal.Scheme.Modules.symmetricCategory X

/-- Degree-one cancellation is the actual evaluation against the hyperplane dual. -/
noncomputable def coordinateHyperplaneBaseCancellationIso (j : σ) :
    IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j) ⊗
      HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j ≅
        𝟙_ (Proj (homogeneousSubmodule σ R)).Modules := by
  let X := Proj (homogeneousSubmodule σ R)
  let M := IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)
  exact InvertibleCancellationPairing.invertibleDualPairingIso M
    (HyperplaneIdeal.MvPolynomial.coordinateHyperplaneIdealModule_isInvertible (R := R) j) ≪≫
    (TensorSections.monoidalUnitObjIso X).symm

/-- Positive and negative powers cancel through the actual dual evaluation. -/
noncomputable def coordinateHyperplanePowerCancellationIso (j : σ) :
    ∀ n : ℕ, TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n ⊗
      TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n ≅
        𝟙_ (Proj (homogeneousSubmodule σ R)).Modules
  | 0 => λ_ (𝟙_ (Proj (homogeneousSubmodule σ R)).Modules)
  | n + 1 =>
      TensorPowerCancellation.tensorSwapMiddleIso
        (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n)
        (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
        (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j) ≪≫
      (coordinateHyperplanePowerCancellationIso j n ⊗ᵢ coordinateHyperplaneBaseCancellationIso j) ≪≫
      λ_ (𝟙_ (Proj (homogeneousSubmodule σ R)).Modules)

set_option backward.isDefEq.respectTransparency false in
/-- Successor cancellation pairs the previous powers and the final factors. -/
theorem coordinateHyperplanePowerCancellationIso_succ_hom (j : σ) (n : ℕ) :
    (TwistShiftIso.MvPolynomial.coordinateHyperplanePowerCancellationIso (R := R) j (n + 1)).hom =
      tensorμ (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n)
        (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
        (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j) ≫
      ((TwistShiftIso.MvPolynomial.coordinateHyperplanePowerCancellationIso (R := R) j n).hom ⊗ₘ
        (coordinateHyperplaneBaseCancellationIso (R := R) j).hom) ≫
      (λ_ (𝟙_ (Proj (homogeneousSubmodule σ R)).Modules)).hom := rfl

/-- The recursively defined positive powers satisfy `O(m+n) ≅ O(m) ⊗ O(n)`. -/
noncomputable def coordinateHyperplanePoleSheafPower_addIso
    (j : σ) :
    ∀ m n : ℕ,
      TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (m + n) ≅
        TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m ⊗
          TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n
  | m, 0 => (ρ_ (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)).symm
  | m, n + 1 =>
      (coordinateHyperplanePoleSheafPower_addIso j m n ⊗ᵢ
          Iso.refl (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j)) ≪≫
        α_ (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m)
          (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
          (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j)

/-- Cancelling equal negative and positive powers gives
`O(-m) ⊗ O(m+n) ≅ O(n)`. -/
noncomputable def
    coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerAddIso
    (j : σ) (m n : ℕ) :
    TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j m ⊗
        TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (m + n) ≅
      TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n := by
  let X := Proj (homogeneousSubmodule σ R)
  let N := TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j m
  let Pm := TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j m
  let Pn := TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n
  let eNP : N ⊗ Pm ≅ 𝟙_ X.Modules :=
    TwistShiftIso.MvPolynomial.coordinateHyperplanePowerCancellationIso (R := R) j m
  exact
    (Iso.refl N ⊗ᵢ
      TwistShiftIso.MvPolynomial.coordinateHyperplanePoleSheafPower_addIso (R := R) j m n) ≪≫
      (α_ N Pm Pn).symm ≪≫
      (eNP ⊗ᵢ Iso.refl Pn) ≪≫
      λ_ Pn

/-- If `m ≤ n`, then `O(-m) ⊗ O(n) ≅ O(n-m)`. -/
noncomputable def
    coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerIsoOfLE
    (j : σ) (m n : ℕ) (h : m ≤ n) :
    TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j m ⊗
        TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n ≅
      TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (n - m) :=
  eqToIso (congrArg
      (fun k ↦ TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j m ⊗
        TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j k)
      (Nat.add_sub_of_le h).symm) ≪≫
    coordinateHyperplaneIdealModulePowerTensorPoleSheafPowerAddIso
      (R := R) j m (n - m)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistShiftIso.MvPolynomial
