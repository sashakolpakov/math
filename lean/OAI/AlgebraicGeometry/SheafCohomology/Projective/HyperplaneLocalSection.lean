/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneCoordinateSection
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FrameSectionComparison
import OAI.AlgebraicGeometry.SheafCohomology.Projective.DualFrameRestriction

/-! # Hyperplane Local Section -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneLocalSection.MvPolynomial

noncomputable section

open _root_.MvPolynomial

open _root_.AlgebraicGeometry _root_.CategoryTheory
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) := fun U => by
  change IsMulCommutative (X.presheaf.obj U)
  exact IsMulCommutative.of_comm fun a b => mul_comm a b

/-- The induced over-site frame on the dual hyperplane ideal. -/
def coordinateHyperplanePoleOverTrivialization (i j : σ) :
    (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j).over (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) ≅
      SheafOfModules.unit ((Proj (homogeneousSubmodule σ R)).ringCatSheaf.over
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)) :=
  Dual.SheafOfModules.dualOverIsoOfIso
    (Proj (homogeneousSubmodule σ R)).ringCatSheaf
    (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
    (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    (HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization (R := R) i j)

theorem coordinateHyperplanePoleSheafTrivialization_eq_restrict (i j : σ) :
    HyperplaneFrames.MvPolynomial.coordinateHyperplanePoleSheafTrivialization (R := R) i j =
      FrameSections.restrictTrivializationOfOverIso
        (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j) (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
        (coordinateHyperplanePoleOverTrivialization (R := R) i j) :=
  DualFrameRestriction.dualRestrictionFrame_eq
    (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
    (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm

theorem coordinateHyperplanePoleSection_coefficient_over (i j : σ) :
    FrameSections.localTrivializationTopSection
      (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j)
      ⟨MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i, MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩
      (FrameSections.restrictTrivializationOfOverIso
        (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j) (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
        (coordinateHyperplanePoleOverTrivialization (R := R) i j))
      (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSection (R := R) j) =
    FrameSections.affineOpenTopSection
      ⟨MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i, MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩
      (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j) :=
  FrameSectionComparison.localTrivializationTopSection_unitHom_apply_one
    (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j)
    ⟨MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i, MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩
    (HyperplanePole.MvPolynomial.coordinateHyperplanePoleUnitHom (R := R) j)
    (coordinateHyperplanePoleOverTrivialization (R := R) i j)
    (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j)
    (HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplanePoleUnitHom_over_comp_trivialization (R := R) i j)

/-- The canonical O(1) section has the hyperplane equation as its affine coordinate. -/
theorem coordinateHyperplanePoleSection_localTrivializationTopSection (i j : σ) :
    FrameSections.localTrivializationTopSection
      (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j)
      ⟨MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i, MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩
      (HyperplaneFrames.MvPolynomial.coordinateHyperplanePoleSheafTrivialization (R := R) i j)
      (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSection (R := R) j) =
    FrameSections.affineOpenTopSection
      ⟨MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i, MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩
      (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j) := by
  rw [coordinateHyperplanePoleSheafTrivialization_eq_restrict]
  exact coordinateHyperplanePoleSection_coefficient_over i j

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneLocalSection.MvPolynomial
