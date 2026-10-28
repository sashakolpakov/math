/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OverScalarRestriction

/-! # Over Frame Scalar Transfer -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.OverFrameScalarTransfer

noncomputable section

/-! Transport of scalar changes from native frames to over-site frames. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

local instance scalarTransferComm (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) := fun U => by
  change IsMulCommutative (X.presheaf.obj U)
  exact IsMulCommutative.of_comm fun a b => mul_comm a b

theorem overTrivializationOfRestrictIso_hom_eq_comp_scalar
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e g : M.restrict U.ι ≅ Invertible.Scheme.Modules.unitObj U.toScheme)
    (r : Γ(X, U))
    (h : e.hom = g.hom ≫
      UnitScalar.unitEndomorphismOfTopSection (OpenFrames.Scheme.Modules.openTopSection U r)) :
    (Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e).hom =
      (Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U g).hom ≫
        Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r := by
  apply (Scheme.Modules.overEquiv U).functor.map_injective
  apply (cancel_mono (U.sheafOfModulesEquivOverUnit X.ringCatSheaf).hom).1
  simp only [Invertible.Scheme.Modules.overTrivializationOfRestrictIso,
    Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage,
    Functor.map_comp, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  erw [OverScalarRestriction.overEquiv_unitScalarEnd]
  simp only [Iso.inv_hom_id, Category.comp_id]
  rw [h]
  rfl

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.OverFrameScalarTransfer
