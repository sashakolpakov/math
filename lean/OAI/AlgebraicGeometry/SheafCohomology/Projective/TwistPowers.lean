/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneFrames
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorSections

/-! # Twist Powers -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial

noncomputable section

open _root_.MvPolynomial

open _root_.AlgebraicGeometry _root_.CategoryTheory MonoidalCategory
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

/-- The nonnegative twists `O(n)` obtained as monoidal powers of the concrete
coordinate-hyperplane `O(1)`. -/
noncomputable def coordinateHyperplanePoleSheafPower (j : σ) :
    ℕ → (Proj (homogeneousSubmodule σ R)).Modules
  | 0 => 𝟙_ (Proj (homogeneousSubmodule σ R)).Modules
  | n + 1 => coordinateHyperplanePoleSheafPower j n ⊗
      HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j

@[simp]
lemma coordinateHyperplanePoleSheafPower_zero (j : σ) :
    TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j 0 =
      𝟙_ (Proj (homogeneousSubmodule σ R)).Modules :=
  rfl

@[simp]
lemma coordinateHyperplanePoleSheafPower_succ (j : σ) (n : ℕ) :
    TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j (n + 1) =
      TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n ⊗
        HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j :=
  rfl

/-- The canonical section of `O(n)`, obtained by starting with `1` in degree
zero and tensoring with the coordinate section in each successor degree. -/
noncomputable def coordinateHyperplanePoleSectionPower (j : σ) :
    ∀ n : ℕ,
      Γ(TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n,
        (⊤ : (Proj (homogeneousSubmodule σ R)).Opens))
  | 0 => TensorSections.monoidalUnitSection
      (Proj (homogeneousSubmodule σ R))
  | n + 1 => TensorSections.tensorSection
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
      (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j) ⊤
      (coordinateHyperplanePoleSectionPower j n)
      (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSection (R := R) j)

/-- A frame of `O(1)` on an open induces compatible frames of all nonnegative
twists on that open. -/
noncomputable def coordinateHyperplanePoleSheafPowerTrivializationOf
    (U : (Proj (homogeneousSubmodule σ R)).Opens) (j : σ)
    (e : (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j).restrict U.ι ≅
      Invertible.Scheme.Modules.unitObj U.toScheme) : ∀ n : ℕ,
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n).restrict U.ι ≅
        Invertible.Scheme.Modules.unitObj U.toScheme
  | 0 => TensorSections.restrictMonoidalUnitIso U.ι ≪≫
      TensorSections.monoidalUnitObjIso U.toScheme
  | n + 1 =>
      TensorSections.restrictMonoidalTensorIso
          U.ι
          (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
          (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j) ≪≫
        (coordinateHyperplanePoleSheafPowerTrivializationOf U j e n ⊗ᵢ e) ≪≫
        TensorSections.unitObjTensorIso U.toScheme

/-- The compatible standard-chart frame of the nonnegative twist `O(n)`. -/
noncomputable def coordinateHyperplanePoleSheafPowerTrivialization
    (i j : σ) : ∀ n : ℕ,
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n).restrict
          (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).ι ≅
        Invertible.Scheme.Modules.unitObj (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).toScheme :=
  TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivializationOf
    (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) j
      (HyperplaneFrames.MvPolynomial.coordinateHyperplanePoleSheafTrivialization (R := R) i j)

/-- Every nonnegative coordinate-hyperplane twist `O(n)` is invertible. -/
theorem coordinateHyperplanePoleSheafPower_isInvertible (j : σ) (n : ℕ) :
    Invertible.Scheme.Modules.IsInvertible
      (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n) := by
  induction n with
  | zero =>
      exact Invertible.Scheme.Modules.isInvertible_unit.of_iso
        (TensorSections.monoidalUnitObjIso
          (Proj (homogeneousSubmodule σ R)))
  | succ n ih =>
      exact (ih.tensorObj
        (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf_isInvertible (R := R) j)).of_iso
          (TensorSections.monoidalTensorObjIso _ _)

/-- The nonnegative powers of the concrete coordinate-hyperplane `O(-1)`. -/
noncomputable def coordinateHyperplaneIdealModulePower (j : σ) :
    ℕ → (Proj (homogeneousSubmodule σ R)).Modules
  | 0 => 𝟙_ (Proj (homogeneousSubmodule σ R)).Modules
  | n + 1 => coordinateHyperplaneIdealModulePower j n ⊗
      IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)

@[simp]
lemma coordinateHyperplaneIdealModulePower_zero (j : σ) :
    TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j 0 =
      𝟙_ (Proj (homogeneousSubmodule σ R)).Modules :=
  rfl

@[simp]
lemma coordinateHyperplaneIdealModulePower_succ (j : σ) (n : ℕ) :
    TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1) =
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n ⊗
        IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j) :=
  rfl

/-- A frame of `O(-1)` on an open induces compatible frames of all its
nonnegative powers on that open. -/
noncomputable def coordinateHyperplaneIdealModulePowerTrivializationOf
    (U : (Proj (homogeneousSubmodule σ R)).Opens) (j : σ)
    (e : (IdealModule.idealModule
        (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)).restrict U.ι ≅
      Invertible.Scheme.Modules.unitObj U.toScheme) : ∀ n : ℕ,
      (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n).restrict U.ι ≅
        Invertible.Scheme.Modules.unitObj U.toScheme
  | 0 => TensorSections.restrictMonoidalUnitIso U.ι ≪≫
      TensorSections.monoidalUnitObjIso U.toScheme
  | n + 1 =>
      TensorSections.restrictMonoidalTensorIso
          U.ι
          (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n)
          (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)) ≪≫
        (coordinateHyperplaneIdealModulePowerTrivializationOf U j e n ⊗ᵢ e) ≪≫
        TensorSections.unitObjTensorIso U.toScheme

/-- The compatible standard-chart frame of the nonnegative power of `O(-1)`. -/
noncomputable def coordinateHyperplaneIdealModulePowerTrivialization
    (i j : σ) : ∀ n : ℕ,
      (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n).restrict
          (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).ι ≅
        Invertible.Scheme.Modules.unitObj (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).toScheme :=
  TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivializationOf
    (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) j
      (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm

/-- Every nonnegative power of the coordinate-hyperplane `O(-1)` is
invertible. -/
theorem coordinateHyperplaneIdealModulePower_isInvertible (j : σ) (n : ℕ) :
    Invertible.Scheme.Modules.IsInvertible
      (TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n) := by
  induction n with
  | zero =>
      exact Invertible.Scheme.Modules.isInvertible_unit.of_iso
        (TensorSections.monoidalUnitObjIso
          (Proj (homogeneousSubmodule σ R)))
  | succ n ih =>
      exact (ih.tensorObj
        (HyperplaneIdeal.MvPolynomial.coordinateHyperplaneIdealModule_isInvertible (R := R) j)).of_iso
          (TensorSections.monoidalTensorObjIso _ _)

/-- The integer twist `O(d)` on polynomial projective space, formed from the
concrete coordinate-hyperplane `O(1)` and `O(-1)`. -/
noncomputable def coordinateHyperplaneTwist (j : σ) :
    ℤ → (Proj (homogeneousSubmodule σ R)).Modules
  | .ofNat n => TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n
  | .negSucc n => TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1)

@[simp]
lemma coordinateHyperplaneTwist_ofNat (j : σ) (n : ℕ) :
    coordinateHyperplaneTwist (R := R) j (.ofNat n) =
      TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n :=
  rfl

@[simp]
lemma coordinateHyperplaneTwist_negSucc (j : σ) (n : ℕ) :
    coordinateHyperplaneTwist (R := R) j (.negSucc n) =
      TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j (n + 1) :=
  rfl

/-- The standard-chart frame of the integer twist `O(d)`. -/
noncomputable def coordinateHyperplaneTwistTrivialization (i j : σ) :
    ∀ d : ℤ,
      (coordinateHyperplaneTwist (R := R) j d).restrict
          (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).ι ≅
        Invertible.Scheme.Modules.unitObj (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).toScheme
  | .ofNat n => coordinateHyperplanePoleSheafPowerTrivialization (R := R) i j n
  | .negSucc n =>
      coordinateHyperplaneIdealModulePowerTrivialization i j (n + 1)

/-- Every integer twist `O(d)` is invertible. -/
theorem coordinateHyperplaneTwist_isInvertible (j : σ) (d : ℤ) :
    Invertible.Scheme.Modules.IsInvertible (coordinateHyperplaneTwist (R := R) j d) := by
  cases d with
  | ofNat n => exact coordinateHyperplanePoleSheafPower_isInvertible j n
  | negSucc n => exact coordinateHyperplaneIdealModulePower_isInvertible j (n + 1)

/-- The constructed twists have genuine finite local presentations. -/
theorem coordinateHyperplaneTwist_finitePresentation (j : σ) (d : ℤ) :
    (coordinateHyperplaneTwist (R := R) j d).IsFinitePresentation :=
  InvertibleFinitePresentation.invertible_finitePresentation
    (coordinateHyperplaneTwist_isInvertible j d)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers.MvPolynomial
