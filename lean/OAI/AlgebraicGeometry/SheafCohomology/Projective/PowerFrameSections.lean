/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistPowers
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneLocalSection
import OAI.AlgebraicGeometry.SheafCohomology.Projective.UnitFrameSection

/-! # Power Frame Sections -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PowerFrameSections.MvPolynomial

noncomputable section

open _root_.MvPolynomial

open _root_.AlgebraicGeometry _root_.CategoryTheory MonoidalCategory
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra
noncomputable local instance (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X

/-- In the standard-chart frame, the canonical section of `O(n)` has
coordinate equal to the `n`th power of the hyperplane's local equation. -/
theorem coordinateHyperplanePoleSectionPower_localTrivializationTopSection
    (i j : σ) (n : ℕ) :
    FrameSections.localTrivializationTopSection
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
        ⟨MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i, MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivialization
          (R := R) i j n)
        (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j n) =
      (FrameSections.affineOpenTopSection
        ⟨MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i, MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩
        (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j)) ^ n := by
  induction n with
  | zero =>
      simpa only [TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower,
        TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower,
        TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivialization,
        TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivializationOf, pow_zero] using
        UnitFrameSection.localTrivializationTopSection_monoidalUnitSection
          ⟨MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i, MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩
  | succ n ih =>
      change FrameSections.localTrivializationTopSection
          (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n ⊗
            HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j)
          ⟨MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i, MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩
          (TensorSections.restrictMonoidalTensorIso
              (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).ι
              (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
              (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j) ≪≫
            (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivialization
                (R := R) i j n ⊗ᵢ
              HyperplaneFrames.MvPolynomial.coordinateHyperplanePoleSheafTrivialization (R := R) i j) ≪≫
            TensorSections.unitObjTensorIso
              (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).toScheme)
          (TensorSections.tensorSection
            (TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n)
            (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j) ⊤
            (TwistPowers.MvPolynomial.coordinateHyperplanePoleSectionPower (R := R) j n)
            (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSection (R := R) j)) = _
      rw [TensorFrameSections.localTrivializationTopSection_tensorSection, ih,
        HyperplaneLocalSection.MvPolynomial.coordinateHyperplanePoleSection_localTrivializationTopSection]
      exact (pow_succ _ n).symm

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PowerFrameSections.MvPolynomial
