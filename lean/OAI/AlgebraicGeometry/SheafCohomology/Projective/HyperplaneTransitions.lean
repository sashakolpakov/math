/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneOverlap
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OverScalarRestriction
import OAI.AlgebraicGeometry.SheafCohomology.Projective.DualOverlapTransition

/-! # Hyperplane Transitions -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneTransitions.MvPolynomial

noncomputable section

open _root_.MvPolynomial

open _root_.AlgebraicGeometry _root_.CategoryTheory
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) := fun U => by
  change IsMulCommutative (X.presheaf.obj U)
  exact IsMulCommutative.of_comm fun a b => mul_comm a b

/-- On a coordinate overlap, the two `O(-1)` generator frames differ by
multiplication by `X_k / X_i`. -/
theorem coordinateHyperplaneIdealModuleTrivialization_restrict_transition
    (i k j : σ) :
    (OpenFrames.Scheme.Modules.restrictOpenTrivialization
        (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)
        (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization
          (R := R) k j).symm).hom =
      (OpenFrames.Scheme.Modules.restrictOpenTrivialization
          (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)
          (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization
            (R := R) i j).symm).hom ≫
        UnitScalar.unitEndomorphismOfTopSection
          (OpenFrames.Scheme.Modules.openTopSection
            (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)
            (CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k :
              Γ(Proj (homogeneousSubmodule σ R),
                CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k))) := by
  let M := IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)
  let tI := OpenFrames.Scheme.Modules.restrictOpenTrivialization
    (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)
    (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm
  let tK := OpenFrames.Scheme.Modules.restrictOpenTrivialization
    (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)
    (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) k j).symm
  let eI := HyperplaneOverlap.MvPolynomial.coordinateHyperplaneIdealOverlapTrivializationLeft
    (R := R) i k j
  let eK := HyperplaneOverlap.MvPolynomial.coordinateHyperplaneIdealOverlapTrivializationRight
    (R := R) i k j
  let u : Γ(Proj (homogeneousSubmodule σ R),
      CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k) :=
    CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k
  change tK.hom = tI.hom ≫
    UnitScalar.unitEndomorphismOfTopSection
      (OpenFrames.Scheme.Modules.openTopSection
        (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k) u)
  have hOver : eK.hom = eI.hom ≫
      Dual.SheafOfModules.overUnitScalarEnd
        (Proj (homogeneousSubmodule σ R)).ringCatSheaf
        (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k) u :=
    HyperplaneOverlap.MvPolynomial.coordinateHyperplaneIdealOverlap_transition (R := R) i k j
  have hScheme :=
    OverScalarRestriction.restrictTrivializationOfOverIso_hom_eq_comp_scalar
      M (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k) eK eI u hOver
  have heI : Invertible.Scheme.Modules.overTrivializationOfRestrictIso M
      (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k) tI = eI := by
    exact OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization
      (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)
      (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm
  have heK : Invertible.Scheme.Modules.overTrivializationOfRestrictIso M
      (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k) tK = eK := by
    exact OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization
      (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)
      (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) k j).symm
  rw [← heK, ← heI] at hScheme
  simpa only [OpenFrames.restrictTrivializationOfOverTrivializationOfRestrictIso]
    using hScheme

/-- The ideal overlap equation with the restriction maps exposed. -/
theorem coordinateHyperplaneIdealOver_restrict_transition (i k j : σ) :
    (Dual.SheafOfModules.restrictOverTrivialization
      (Proj (homogeneousSubmodule σ R)).ringCatSheaf
      (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)
      (Invertible.Scheme.Modules.overTrivializationOfRestrictIso _ _
        (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) k j).symm)
      (Over.mk (homOfLE (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)))).hom =
    (Dual.SheafOfModules.restrictOverTrivialization
      (Proj (homogeneousSubmodule σ R)).ringCatSheaf
      (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
      (Invertible.Scheme.Modules.overTrivializationOfRestrictIso _ _
        (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm)
      (Over.mk (homOfLE (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)))).hom ≫
      Dual.SheafOfModules.overUnitScalarEnd
        (Proj (homogeneousSubmodule σ R)).ringCatSheaf
        (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)
        (CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k :
          Γ(Proj (homogeneousSubmodule σ R), CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)) :=
  HyperplaneOverlap.MvPolynomial.coordinateHyperplaneIdealOverlap_transition (R := R) i k j

/-- On a coordinate overlap, the dual frames differ by X_k / X_i. -/
theorem coordinateHyperplanePoleSheafTrivialization_restrict_transition
    (i k j : σ) :
    let X := Proj (homogeneousSubmodule σ R)
    let M := IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)
    let U := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i
    let V := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k
    let W := CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k
    let e := (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm
    let g := (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) k j).symm
    let s : Γ(X, W) := CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k
    (OpenFrames.Scheme.Modules.restrictOpenTrivialization
      (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)
      (Dual.Scheme.Modules.dualRestrictIsoOfRestrictIso M U e)).hom =
    (OpenFrames.Scheme.Modules.restrictOpenTrivialization
      (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)
      (Dual.Scheme.Modules.dualRestrictIsoOfRestrictIso M V g)).hom ≫
      UnitScalar.unitEndomorphismOfTopSection
        (OpenFrames.Scheme.Modules.openTopSection W s) := by
  exact DualOverlapTransition.dualOpenOverlap_transition
    (X := Proj (homogeneousSubmodule σ R))
    (U := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) (V := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)
    (W := CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)
    (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
    (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)
    (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)
    (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm
    (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) k j).symm
    (CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k :
      Γ(Proj (homogeneousSubmodule σ R), CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k))
    (coordinateHyperplaneIdealOver_restrict_transition (R := R) i k j)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneTransitions.MvPolynomial
