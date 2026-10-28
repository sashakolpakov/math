/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenFrames

/-! # Over Scalar Restriction -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.OverScalarRestriction

noncomputable section

/-! Scalar transition maps under the open-subscheme equivalence. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) := fun U => by
  change IsMulCommutative (X.presheaf.obj U)
  exact IsMulCommutative.of_comm fun a b => mul_comm a b

theorem overEquiv_unitScalarEnd {X : Scheme.{u}} (U : X.Opens) (s : Γ(X, U)) :
    (Scheme.Modules.overEquiv U).functor.map
        (Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U s) ≫
      (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom =
    (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom ≫
      UnitScalar.unitEndomorphismOfTopSection (OpenFrames.Scheme.Modules.openTopSection U s) := by
  apply _root_.SheafOfModules.hom_ext
  ext W
  change (1 : Γ(X, (U.overEquivalence.inverse.obj W.unop).left)) *
      X.presheaf.map (U.overEquivalence.inverse.obj W.unop).hom.op s =
    (1 : Γ(U.toScheme, W.unop)) *
      U.toScheme.presheaf.map W.unop.leTop.op (U.topIso.inv s)
  rw [one_mul, one_mul, Scheme.Opens.topIso_inv]
  change X.presheaf.map (U.overEquivalence.inverse.obj W.unop).hom.op s =
    X.presheaf.map (U.ι.opensFunctor.map W.unop.leTop).op
      (X.presheaf.map (eqToHom U.ι_image_top).op s)
  rw [← X.presheaf.map_comp_apply]
  congr 1

theorem restrictTrivializationOfOverIso_hom_eq_comp_scalar
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e g : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U))
    (s : Γ(X, U))
    (h : e.hom = g.hom ≫ Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U s) :
    (FrameSections.restrictTrivializationOfOverIso M U e).hom =
      (FrameSections.restrictTrivializationOfOverIso M U g).hom ≫
        UnitScalar.unitEndomorphismOfTopSection (OpenFrames.Scheme.Modules.openTopSection U s) := by
  simp only [FrameSections.restrictTrivializationOfOverIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [h, Functor.map_comp]
  simp only [Category.assoc]
  rw [overEquiv_unitScalarEnd]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.OverScalarRestriction
