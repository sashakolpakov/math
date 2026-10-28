/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneFrames
import OAI.AlgebraicGeometry.SheafCohomology.Projective.IdealOverFrame
import OAI.AlgebraicGeometry.SheafCohomology.Projective.DualFrameScalar

/-! # Hyperplane Coordinate Section -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneCoordinateSection.MvPolynomial

noncomputable section

open _root_.MvPolynomial

open _root_.AlgebraicGeometry _root_.CategoryTheory
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) :=
  fun U ↦ by
    change IsMulCommutative (X.presheaf.obj U)
    exact IsMulCommutative.of_comm fun a b ↦ mul_comm a b

noncomputable def coordinateHyperplaneIdealOverTrivialization
    (i j : σ) :
    (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)).over
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) ≅
      SheafOfModules.unit
        ((Proj (homogeneousSubmodule σ R)).ringCatSheaf.over
          (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)) :=
  Invertible.Scheme.Modules.overTrivializationOfRestrictIso _ _
    (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm

theorem coordinateHyperplaneIdealOverTrivialization_inv_comp
    (i j : σ) :
    (coordinateHyperplaneIdealOverTrivialization (R := R) i j).inv ≫
        (IdealModule.idealModuleToUnit
          (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)).over
            (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) =
      Dual.SheafOfModules.overUnitScalarEnd
        (Proj (homogeneousSubmodule σ R)).ringCatSheaf
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
        (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j) := by
  let : IsClosedImmersion (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j) :=
    SpaceHyperplane.MvPolynomial.coordinateHyperplaneι_isClosedImmersion j
  let : QuasiCompact (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j) := inferInstance
  let U : (Proj (homogeneousSubmodule σ R)).affineOpens :=
    ⟨MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i, MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩
  let r := CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j
  have hr : r ∈ (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j).ker.ideal U := by
    rw [CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_span]
    exact Ideal.mem_span_singleton_self r
  simpa only [coordinateHyperplaneIdealOverTrivialization,
    HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization] using
      IdealOverFrame.localIdealGeneratorOverTrivialization_inv_comp
        (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j) U r hr
          (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_span i j)
          (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_mem_nonZeroDivisors i j)

/-- In a standard-chart frame, the canonical coordinate section of `O(1)` is
multiplication by the local equation of the coordinate hyperplane. -/
theorem coordinateHyperplanePoleUnitHom_over_comp_trivialization
    (i j : σ) :
    ((HyperplanePole.MvPolynomial.coordinateHyperplanePoleUnitHom (R := R) j).over
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)) ≫
        (Dual.SheafOfModules.dualOverIsoOfIso
          (Proj (homogeneousSubmodule σ R)).ringCatSheaf
          (IdealModule.idealModule
            (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
          (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
          (Invertible.Scheme.Modules.overTrivializationOfRestrictIso _ _
            (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization
              (R := R) i j).symm)).hom =
      Dual.SheafOfModules.overUnitScalarEnd
        (Proj (homogeneousSubmodule σ R)).ringCatSheaf
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
        (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j) := by
  exact DualFrameScalar.dualMap_over_comp_dualOverIsoOfIso_hom_eq_scalar
    (IdealModule.idealModuleToUnit
      (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
    (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    (coordinateHyperplaneIdealOverTrivialization (R := R) i j)
    (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j)
    (coordinateHyperplaneIdealOverTrivialization_inv_comp (R := R) i j)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneCoordinateSection.MvPolynomial
