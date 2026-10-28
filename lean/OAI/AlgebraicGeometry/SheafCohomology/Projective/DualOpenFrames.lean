/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenFrames
import OAI.AlgebraicGeometry.SheafCohomology.Projective.DualFrameRestriction

/-! # Dual Open Frames -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.DualOpenFrames

noncomputable section

/-! Duality commutes with restriction of the actual local rank-one frames. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u

local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) := fun U => by
  change IsMulCommutative (X.presheaf.obj U)
  exact IsMulCommutative.of_comm fun a b => mul_comm a b

theorem dualOverFrame_restrict {X : Scheme.{u}} (M : X.Modules)
    {U V : X.Opens} (hVU : V ≤ U)
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf
      (Dual.Scheme.Modules.dualObj M) U
      (Dual.SheafOfModules.dualOverIsoOfIso X.ringCatSheaf M U e)
      (Over.mk (homOfLE hVU)) =
    Dual.SheafOfModules.dualOverIsoOfIso X.ringCatSheaf M V
      (Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U e
        (Over.mk (homOfLE hVU))) := by
  apply Iso.ext
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  rfl

theorem restrictOpenTrivialization_dualRestrictIsoOfRestrictIso
    {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (hVU : V ≤ U)
    (e : M.restrict U.ι ≅ Invertible.Scheme.Modules.unitObj U.toScheme) :
    OpenFrames.Scheme.Modules.restrictOpenTrivialization hVU
      (Dual.Scheme.Modules.dualRestrictIsoOfRestrictIso M U e) =
    FrameSections.restrictTrivializationOfOverIso (Dual.Scheme.Modules.dualObj M) V
      (Dual.SheafOfModules.dualOverIsoOfIso X.ringCatSheaf M V
        (Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U
          (Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e)
          (Over.mk (homOfLE hVU)))) := by
  rw [OpenFrames.Scheme.Modules.restrictOpenTrivialization, DualFrameRestriction.dualRestrictionFrame_eq,
    OpenFrames.overTrivializationOfRestrictTrivializationOfOverIso, dualOverFrame_restrict]

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.DualOpenFrames
