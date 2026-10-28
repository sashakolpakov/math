/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneCoordinateSection
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OverFrameTransitions

/-! # Hyperplane Overlap -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneOverlap.MvPolynomial

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

noncomputable def coordinateHyperplaneIdealOverlapTrivializationLeft
    (i k j : σ) :
    (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)).over
        (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k) ≅
      SheafOfModules.unit
        ((Proj (homogeneousSubmodule σ R)).ringCatSheaf.over
          (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)) :=
  Dual.SheafOfModules.restrictOverTrivialization
    (Proj (homogeneousSubmodule σ R)).ringCatSheaf
    (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
    (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    (HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization (R := R) i j)
    (Over.mk (homOfLE (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)))

noncomputable def coordinateHyperplaneIdealOverlapTrivializationRight
    (i k j : σ) :
    (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)).over
        (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k) ≅
      SheafOfModules.unit
        ((Proj (homogeneousSubmodule σ R)).ringCatSheaf.over
          (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)) :=
  Dual.SheafOfModules.restrictOverTrivialization
    (Proj (homogeneousSubmodule σ R)).ringCatSheaf
    (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
    (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)
    (HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization (R := R) k j)
    (Over.mk (homOfLE (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)))

theorem coordinateHyperplaneIdealOverlapTrivializationLeft_inv_comp
    (i k j : σ) :
    (coordinateHyperplaneIdealOverlapTrivializationLeft
        (R := R) i k j).inv ≫
        (IdealModule.idealModuleToUnit
          (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)).over
            (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k) =
      Dual.SheafOfModules.overUnitScalarEnd
        (Proj (homogeneousSubmodule σ R)).ringCatSheaf
        (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)
        ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)).op
          (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j)) := by
  simpa only [coordinateHyperplaneIdealOverlapTrivializationLeft] using
    OverFrameTransitions.restrictOverTrivialization_inv_comp_over
      (IdealModule.idealModuleToUnit
        (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
      (HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization (R := R) i j)
      (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j)
      (HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization_inv_comp (R := R) i j)
      (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)

theorem coordinateHyperplaneIdealOverlapTrivializationRight_inv_comp
    (i k j : σ) :
    (coordinateHyperplaneIdealOverlapTrivializationRight
        (R := R) i k j).inv ≫
        (IdealModule.idealModuleToUnit
          (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)).over
            (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k) =
      Dual.SheafOfModules.overUnitScalarEnd
        (Proj (homogeneousSubmodule σ R)).ringCatSheaf
        (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)
        ((Proj (homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)).op
          (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) k j)) := by
  simpa only [coordinateHyperplaneIdealOverlapTrivializationRight] using
    OverFrameTransitions.restrictOverTrivialization_inv_comp_over
      (IdealModule.idealModuleToUnit
        (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
      (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) k)
      (HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization (R := R) k j)
      (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) k j)
      (HyperplaneCoordinateSection.MvPolynomial.coordinateHyperplaneIdealOverTrivialization_inv_comp (R := R) k j)
      (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)

theorem coordinateHyperplaneIdealOverlap_transition (i k j : σ) :
    (coordinateHyperplaneIdealOverlapTrivializationRight
        (R := R) i k j).hom =
      (coordinateHyperplaneIdealOverlapTrivializationLeft
          (R := R) i k j).hom ≫
        Dual.SheafOfModules.overUnitScalarEnd
          (Proj (homogeneousSubmodule σ R)).ringCatSheaf
          (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)
          (CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k :
            Γ(Proj (homogeneousSubmodule σ R),
              CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)) := by
  let eI := coordinateHyperplaneIdealOverlapTrivializationLeft
    (R := R) i k j
  let eK := coordinateHyperplaneIdealOverlapTrivializationRight
    (R := R) i k j
  let inc :
      (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)).over
          (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k) ⟶
        SheafOfModules.unit
          ((Proj (homogeneousSubmodule σ R)).ringCatSheaf.over
            (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)) :=
    (IdealModule.idealModuleToUnit
      (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)).over
        (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)
  let rI := (Proj (homogeneousSubmodule σ R)).presheaf.map
    (homOfLE (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_left (R := R) i k)).op
    (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j)
  let rK := (Proj (homogeneousSubmodule σ R)).presheaf.map
    (homOfLE (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_le_right (R := R) i k)).op
    (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) k j)
  let u : Γ(Proj (homogeneousSubmodule σ R),
      CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k) :=
    CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k
  let sI := Dual.SheafOfModules.overUnitScalarEnd
    (Proj (homogeneousSubmodule σ R)).ringCatSheaf
    (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k) rI
  let sK := Dual.SheafOfModules.overUnitScalarEnd
    (Proj (homogeneousSubmodule σ R)).ringCatSheaf
    (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k) rK
  let sU := Dual.SheafOfModules.overUnitScalarEnd
    (Proj (homogeneousSubmodule σ R)).ringCatSheaf
    (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k) u
  change eK.hom = eI.hom ≫ sU
  have hI : eI.inv ≫ inc = sI :=
    coordinateHyperplaneIdealOverlapTrivializationLeft_inv_comp
      (R := R) i k j
  have hK : eK.inv ≫ inc = sK :=
    coordinateHyperplaneIdealOverlapTrivializationRight_inv_comp
      (R := R) i k j
  have hr : rI = u * rK :=
    CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_restrict_eq_transition_mul
      (R := R) i k j
  have hmul :=
    (Dual.SheafOfModules.overUnitScalarEndRingHom
      (Proj (homogeneousSubmodule σ R)).ringCatSheaf
      (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)).map_mul rK u
  change Dual.SheafOfModules.overUnitScalarEnd
      (Proj (homogeneousSubmodule σ R)).ringCatSheaf
        (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k) (rK * u) =
    Dual.SheafOfModules.overUnitScalarEnd
        (Proj (homogeneousSubmodule σ R)).ringCatSheaf
          (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k) u ≫
      Dual.SheafOfModules.overUnitScalarEnd
        (Proj (homogeneousSubmodule σ R)).ringCatSheaf
          (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k) rK at hmul
  have hscalar : sI = sU ≫ sK := by
    dsimp only [sI, sU, sK]
    rw [hr, mul_comm u rK]
    exact hmul
  have : Mono inc := OverFrameTransitions.sheafOfModules_mono_over
    (IdealModule.idealModuleToUnit (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
    (OverFrameTransitions.idealModuleToUnit_mono
      (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
    (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)
  have hmonoComp : Mono (eK.inv ≫ inc) :=
    @mono_comp _ _ _ _ _ eK.inv inferInstance inc inferInstance
  have : Mono sK := by
    rw [← hK]
    exact hmonoComp
  apply (cancel_mono sK).1
  calc
    eK.hom ≫ sK = eK.hom ≫ (eK.inv ≫ inc) :=
      congrArg (fun q ↦ eK.hom ≫ q) hK.symm
    _ = inc := eK.hom_inv_id_assoc inc
    _ = eI.hom ≫ (eI.inv ≫ inc) := (eI.hom_inv_id_assoc inc).symm
    _ = eI.hom ≫ sI := congrArg (fun q ↦ eI.hom ≫ q) hI
    _ = eI.hom ≫ (sU ≫ sK) :=
      congrArg (fun q ↦ eI.hom ≫ q) hscalar
    _ = (eI.hom ≫ sU) ≫ sK := (Category.assoc _ _ _).symm

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneOverlap.MvPolynomial
