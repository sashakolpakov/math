/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistFrameRestriction
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OverlapTopUnit

/-! # Integer Twist Transitions -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.IntegerTwistTransitions.MvPolynomial

noncomputable section

open _root_.MvPolynomial

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

private lemma coordinateOpenTransitionTopUnit_zpow_ofNat_coe (i k : σ) (n : ℕ) :
    ((OverlapTopUnit.MvPolynomial.coordinateOpenTransitionTopUnit (R := R) i k ^ (.ofNat n : ℤ) :
        Γ((CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme,
          (⊤ : (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme.Opens))ˣ) :
      Γ((CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme,
        (⊤ : (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme.Opens))) =
      OpenFrames.Scheme.Modules.openTopSection (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)
        (CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k :
          Γ(Proj (homogeneousSubmodule σ R),
            CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)) ^ n := by
  change (((OverlapTopUnit.MvPolynomial.coordinateOpenTransitionTopUnit (R := R) i k) ^ n :
      Γ((CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme,
        (⊤ : (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme.Opens))ˣ) :
    Γ((CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme,
      (⊤ : (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme.Opens))) = _
  rw [Units.val_pow_eq_pow_val]
  exact congrArg (fun q => q ^ n)
    (OverlapTopUnit.MvPolynomial.coordinateOpenTransitionTopUnit_coe (R := R) i k)

/-- On a coordinate overlap, the two standard frames of `O(d)` differ by the
integer power of `X_k / X_i`. -/
theorem coordinateHyperplaneTwistTrivialization_restrict_transition
    (i k j : σ) : ∀ d : ℤ,
    (OpenFrames.Scheme.Modules.restrictOpenTrivialization
        (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := R) i j d)).hom =
      (OpenFrames.Scheme.Modules.restrictOpenTrivialization
          (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)
          (TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := R) k j d)).hom ≫
        UnitScalar.unitEndomorphismOfTopSection
          ((OverlapTopUnit.MvPolynomial.coordinateOpenTransitionTopUnit (R := R) i k ^ d :
              Γ((CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme,
                (⊤ : (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme.Opens))ˣ) :
            Γ((CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme,
              (⊤ : (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme.Opens))) := by
  intro d
  cases d with
  | ofNat n =>
      simpa only [TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization,
        TwistPowers.MvPolynomial.coordinateHyperplaneTwist_ofNat,
        coordinateOpenTransitionTopUnit_zpow_ofNat_coe] using
        TwistFrameRestriction.MvPolynomial.coordinateHyperplanePoleSheafPowerTrivialization_restrict_transition
          (R := R) i k j n
  | negSucc n =>
      let U := CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k
      let t := OverlapTopUnit.MvPolynomial.coordinateOpenTransitionTopUnit (R := R) i k
      let A := UnitScalar.unitAutomorphismOfTopUnit (t ^ (n + 1))
      have h := NegativeTwistTransitions.MvPolynomial.coordinateHyperplaneIdealModulePowerTrivialization_restrict_transition
        (R := R) i k j (n + 1)
      have htPow :
          ((t ^ (n + 1) : Γ(U.toScheme, (⊤ : U.toScheme.Opens))ˣ) :
              Γ(U.toScheme, (⊤ : U.toScheme.Opens))) =
            OpenFrames.Scheme.Modules.openTopSection U
              (CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k :
                Γ(Proj (homogeneousSubmodule σ R), U)) ^ (n + 1) := by
        rw [Units.val_pow_eq_pow_val]
        exact congrArg (fun q => q ^ (n + 1))
          (OverlapTopUnit.MvPolynomial.coordinateOpenTransitionTopUnit_coe (R := R) i k)
      have hA :
          (OpenFrames.Scheme.Modules.restrictOpenTrivialization
              (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)
              (TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization
                (R := R) k j (.negSucc n))).hom =
            (OpenFrames.Scheme.Modules.restrictOpenTrivialization
                (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)
                (TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization
                  (R := R) i j (.negSucc n))).hom ≫ A.hom := by
        change _ = _ ≫ UnitScalar.unitEndomorphismOfTopSection
          ((t ^ (n + 1) : Γ(U.toScheme, (⊤ : U.toScheme.Opens))ˣ) :
            Γ(U.toScheme, (⊤ : U.toScheme.Opens)))
        rw [htPow]
        exact h
      have hInv : A.inv =
          UnitScalar.unitEndomorphismOfTopSection
            ((OverlapTopUnit.MvPolynomial.coordinateOpenTransitionTopUnit (R := R) i k ^
                (.negSucc n : ℤ) :
              Γ(U.toScheme, (⊤ : U.toScheme.Opens))ˣ) :
                Γ(U.toScheme, (⊤ : U.toScheme.Opens))) := by
        simp only [A, t, UnitScalar.unitAutomorphismOfTopUnit]
        rw [zpow_negSucc]
      rw [← hInv, hA]
      simp only [Category.assoc, A.hom_inv_id, Category.comp_id]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.IntegerTwistTransitions.MvPolynomial
