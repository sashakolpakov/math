/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Dual

/-! # Dual Frame Scalar -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.DualFrameScalar

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.SheafOfModules
universe u

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) := fun U => by
  change IsMulCommutative (X.presheaf.obj U)
  exact IsMulCommutative.of_comm fun a b => mul_comm a b

theorem dualMap_over_comp_dualOverIsoOfIso_hom_eq_scalar
    {X : Scheme.{u}} {M : X.Modules}
    (i : M ⟶ Invertible.Scheme.Modules.unitObj X) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (r : Γ(X, U))
    (h : e.inv ≫ i.over U =
      Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r) :
    (((Dual.Scheme.Modules.dualUnitObjIso (X := X)).inv ≫
      Dual.Scheme.Modules.dualMapObj i).over U) ≫
        (Dual.SheafOfModules.dualOverIsoOfIso
          X.ringCatSheaf M U e).hom =
      Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r := by
  apply (Dual.SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U).injective
  have hr : (Dual.SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U)
      (Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r) = r := by
    change (Dual.SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U)
      ((Dual.SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U).symm r) = r
    exact (Dual.SheafOfModules.dualUnitSectionsEquiv
      X.ringCatSheaf U).apply_symm_apply r
  rw [hr]
  change
    (Hom.over ((Dual.Scheme.Modules.dualUnitObjIso (X := X)).inv ≫
        Dual.Scheme.Modules.dualMapObj i) U ≫
      (Dual.SheafOfModules.dualOverIsoOfIso
        X.ringCatSheaf M U e).hom).val.app (.op (Over.mk (𝟙 U)))
          (show (X.ringCatSheaf.over U).obj.obj
            (.op (Over.mk (𝟙 U))) from 1) = r
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  change Dual.SheafOfModules.dualTrivializationLinearEquiv
      X.ringCatSheaf M U e
        (Dual.SheafOfModules.dualPrecomp X.ringCatSheaf i U
          ((Dual.SheafOfModules.dualUnitLinearEquiv
            X.ringCatSheaf U).symm 1)) = r
  change Dual.SheafOfModules.dualUnitLinearEquiv X.ringCatSheaf U
      (e.inv ≫ (i.over U ≫
        (Dual.SheafOfModules.dualUnitLinearEquiv
          X.ringCatSheaf U).symm 1)) = r
  let alpha := (Dual.SheafOfModules.dualUnitLinearEquiv
    X.ringCatSheaf U).symm 1
  have hcomp : (e.inv ≫ i.over U) ≫ alpha =
      Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r ≫ alpha :=
    congrArg (fun q ↦ q ≫ alpha) h
  have halpha : alpha = 𝟙 _ := by
    change Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U 1 = 𝟙 _
    exact (Dual.SheafOfModules.overUnitScalarEndRingHom
      X.ringCatSheaf U).map_one
  change Dual.SheafOfModules.dualUnitLinearEquiv X.ringCatSheaf U
      (e.inv ≫ (i.over U ≫ alpha)) = r
  have h₁ : Dual.SheafOfModules.dualUnitLinearEquiv X.ringCatSheaf U
      (e.inv ≫ (i.over U ≫ alpha)) =
      Dual.SheafOfModules.dualUnitLinearEquiv X.ringCatSheaf U
        ((e.inv ≫ i.over U) ≫ alpha) :=
    congrArg _ (Category.assoc _ _ _).symm
  have h₂ : Dual.SheafOfModules.dualUnitLinearEquiv X.ringCatSheaf U
      ((e.inv ≫ i.over U) ≫ alpha) =
      Dual.SheafOfModules.dualUnitLinearEquiv X.ringCatSheaf U
        (Dual.SheafOfModules.overUnitScalarEnd
          X.ringCatSheaf U r ≫ alpha) := congrArg _ hcomp
  have h₃ : Dual.SheafOfModules.dualUnitLinearEquiv X.ringCatSheaf U
      (Dual.SheafOfModules.overUnitScalarEnd
        X.ringCatSheaf U r ≫ alpha) = r := by
    rw [halpha, Category.comp_id]
    change (Dual.SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U)
      (Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r) = r
    exact hr
  exact h₁.trans (h₂.trans h₃)

end OAI.AlgebraicGeometry.SheafCohomology.Projective.DualFrameScalar
