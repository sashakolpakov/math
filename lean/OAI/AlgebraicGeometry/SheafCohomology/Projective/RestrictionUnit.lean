/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Invertible

/-! # Restriction Unit -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.RestrictionUnit

/-! The restriction/pullback comparison respects the canonical structure module. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

theorem restrictAdjunction_unitHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] :
    (Scheme.Modules.restrictAdjunction f).homEquiv _ _
      (Scheme.Modules.restrictUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  apply SheafOfModules.hom_ext
  ext U
  change (f.appIso (f ⁻¹ᵁ U.unop)).hom
      (Y.presheaf.map (homOfLE (f.image_preimage_le U.unop)).op
        (1 : Γ(Y, U.unop))) = f.app U.unop 1
  simp only [map_one]

theorem restrictFunctorIsoPullback_inv_comp_restrictUnitIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (Scheme.Modules.restrictFunctorIsoPullback f).inv.app
      (Invertible.Scheme.Modules.unitObj Y) ≫ (Scheme.Modules.restrictUnitIso f).hom =
      (Invertible.Scheme.Modules.pullbackUnitIso f).hom := by
  let er := (Scheme.Modules.restrictFunctorIsoPullback f).app (Invertible.Scheme.Modules.unitObj Y)
  apply (cancel_epi er.hom).1
  change er.hom ≫ er.inv ≫ (Scheme.Modules.restrictUnitIso f).hom = _
  rw [Iso.hom_inv_id_assoc]
  apply ((Scheme.Modules.restrictAdjunction f).homEquiv _ _).injective
  rw [restrictAdjunction_unitHom, Adjunction.homEquiv_naturality_right]
  change _ = ((Scheme.Modules.restrictAdjunction f).homEquiv _ _
    (((Scheme.Modules.restrictAdjunction f).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction f)).hom.app
        (Invertible.Scheme.Modules.unitObj Y))) ≫ _
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  exact (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom).symm

end OAI.AlgebraicGeometry.SheafCohomology.Projective.RestrictionUnit
