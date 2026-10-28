/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechFactors
import OAI.AlgebraicGeometry.SheafCohomology.Projective.IntegerTwistTransitions

/-! # Twist Cech First Frame -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechFirstFrame.MvPolynomial

noncomputable section

open _root_.MvPolynomial

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite _root_.TopologicalSpace
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Deleting the first Cech entry changes the anchor frame by the restricted
integer power of the standard-chart transition unit. -/
theorem coordinateHyperplaneTwistCechTrivialization_restrict_delete_zero
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (j : σ) (d : ℤ) :
    (TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistCechTrivialization (R := R) a.1 j d).hom =
      (OpenFrames.Scheme.Modules.restrictOpenTrivialization
          (TwistCechFactors.MvPolynomial.coordinateOpenCechDelete_le (R := R) a 0)
          (TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistCechTrivialization
            (R := R) (a.delete 0).1 j d)).hom ≫
        UnitScalar.unitEndomorphismOfTopSection
          ((TwistCechFactors.MvPolynomial.coordinateOpenCechFirstTransitionTopUnit (R := R) a ^ d :
              Γ((StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1).toScheme,
                (⊤ : (StandardCech.MvPolynomial.coordinateOpenCechIntersection
                  (R := R) a.1).toScheme.Opens))ˣ) :
            Γ((StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1).toScheme,
              (⊤ : (StandardCech.MvPolynomial.coordinateOpenCechIntersection
                (R := R) a.1).toScheme.Opens))) := by
  let i := (a.1 0).down
  let k := (a.1 1).down
  let U := CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k
  let V := StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1
  let hVU := TwistCechFactors.MvPolynomial.coordinateOpenCechIntersection_le_firstOverlap (R := R) a
  let eI := OpenFrames.Scheme.Modules.restrictOpenTrivialization
    (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)
    (TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := R) i j d)
  let eK := OpenFrames.Scheme.Modules.restrictOpenTrivialization
    (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)
    (TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization (R := R) k j d)
  let r : Γ(Proj (homogeneousSubmodule σ R), U) :=
    ((CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k ^ d :
      Γ(Proj (homogeneousSubmodule σ R), U)ˣ) :
      Γ(Proj (homogeneousSubmodule σ R), U))
  have hOverlap : eI.hom = eK.hom ≫
      UnitScalar.unitEndomorphismOfTopSection
        (OpenFrames.Scheme.Modules.openTopSection U r) := by
    rw [← TwistCechFactors.MvPolynomial.coordinateOpenTransitionTopUnit_zpow_coe_aux]
    exact IntegerTwistTransitions.MvPolynomial.coordinateHyperplaneTwistTrivialization_restrict_transition
      (R := R) i k j d
  have hV := TwistCechFactors.MvPolynomial.restrictOpenTrivialization_hom_eq_comp_scalar_aux
    (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d) hVU eI eK r hOverlap
  have hIFrame :
      TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistCechTrivialization (R := R) a.1 j d =
        OpenFrames.Scheme.Modules.restrictOpenTrivialization hVU eI := by
    rw [TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistCechTrivialization]
    dsimp only [eI]
    rw [OpenFrameTransitivity.Scheme.Modules.restrictOpenTrivialization_comp]
  have hKFrame :
      OpenFrames.Scheme.Modules.restrictOpenTrivialization
          (TwistCechFactors.MvPolynomial.coordinateOpenCechDelete_le (R := R) a 0)
          (TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistCechTrivialization
            (R := R) (a.delete 0).1 j d) =
        OpenFrames.Scheme.Modules.restrictOpenTrivialization hVU eK := by
    rw [TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistCechTrivialization]
    dsimp only [eK]
    rw [OpenFrameTransitivity.Scheme.Modules.restrictOpenTrivialization_comp,
      OpenFrameTransitivity.Scheme.Modules.restrictOpenTrivialization_comp]
    dsimp only [k]
    change OpenFrames.Scheme.Modules.restrictOpenTrivialization _
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization
          (R := R) (a.1 1).down j d) =
      OpenFrames.Scheme.Modules.restrictOpenTrivialization _
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwistTrivialization
          (R := R) (a.1 1).down j d)
    rfl
  rw [hIFrame, hKFrame,
    TwistCechFactors.MvPolynomial.coordinateOpenCechFirstTransitionTopUnit_zpow_coe]
  exact hV

/-- Every noninitial Cech face is ordinary restriction in the chosen twist
coordinates. -/
theorem coordinateHyperplaneTwistBaseCechFactorIsoUnit_naturality_delete_of_ne_zero
    [LinearOrder σ] {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n + 1))
    (k : Fin (n + 2)) (hk : k ≠ 0) (j : σ) (d : ℤ) :
    (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d)).map
          (StandardCech.MvPolynomial.coordinateOpenCechDelete (R := R) a k).op ≫
      (TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit
        (R := R) a.1 j d).hom =
    (TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistBaseCechFactorIsoUnit
        (R := R) (a.delete k).1 j d).hom ≫
      (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
        (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
          (StandardCech.MvPolynomial.coordinateOpenCechDelete (R := R) a k).op := by
  let M := TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := R) j d
  let U := StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) (a.delete k).1
  let V := StandardCech.MvPolynomial.coordinateOpenCechIntersection (R := R) a.1
  let hVU := TwistCechFactors.MvPolynomial.coordinateOpenCechDelete_le (R := R) a k
  let eU := Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U
    (TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistCechTrivialization (R := R) (a.delete k).1 j d)
  have hframe :=
    TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistCechTrivialization_restrict_delete_of_ne_zero
      (R := R) a k hk j d
  have hover :
      Invertible.Scheme.Modules.overTrivializationOfRestrictIso M V
          (TwistCechFactors.MvPolynomial.coordinateHyperplaneTwistCechTrivialization (R := R) a.1 j d) =
        Dual.SheafOfModules.restrictOverTrivialization
          (Proj (homogeneousSubmodule σ R)).ringCatSheaf M U eU
            (Over.mk (homOfLE hVU)) := by
    rw [← hframe]
    exact OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization hVU _
  change (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) M).map (homOfLE hVU).op ≫
    (TwistCechFactors.MvPolynomial.baseModulePresheafObjIsoUnitOfOverIso
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) M V _).hom =
    (TwistCechFactors.MvPolynomial.baseModulePresheafObjIsoUnitOfOverIso
      (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) M U eU).hom ≫
      (Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf
        (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ))
          (Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)))).map
            (homOfLE hVU).op
  rw [hover]
  exact TwistCechFactors.MvPolynomial.baseModulePresheafObjIsoUnitOfOverIso_naturality
    (MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := R) (σ := σ)) M hVU eU

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistCechFirstFrame.MvPolynomial
