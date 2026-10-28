/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenFrames

/-! # Open Frame Transitivity -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenFrameTransitivity

noncomputable section

open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules

/-! Transitivity of the actual restriction operation on local frames. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory
universe u
section

theorem restrictOverTrivialization_comp {X : Scheme.{u}} (M : X.Modules)
    {U V W : X.Opens} (hVU : V ≤ U) (hWV : W ≤ V)
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M V
      (Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U e
        (Over.mk (homOfLE hVU))) (Over.mk (homOfLE hWV)) =
    Dual.SheafOfModules.restrictOverTrivialization X.ringCatSheaf M U e
      (Over.mk (homOfLE (hWV.trans hVU))) := by
  apply Iso.ext
  apply _root_.SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro Z
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end

namespace Scheme.Modules

theorem restrictOpenTrivialization_comp {X : Scheme.{u}} {M : X.Modules}
    {U V W : X.Opens} (hVU : V ≤ U) (hWV : W ≤ V)
    (e : M.restrict U.ι ≅ Invertible.Scheme.Modules.unitObj U.toScheme) :
    OpenFrames.Scheme.Modules.restrictOpenTrivialization hWV (OpenFrames.Scheme.Modules.restrictOpenTrivialization hVU e) =
      OpenFrames.Scheme.Modules.restrictOpenTrivialization (hWV.trans hVU) e := by
  unfold OpenFrames.Scheme.Modules.restrictOpenTrivialization
  rw [OpenFrames.overTrivializationOfRestrictTrivializationOfOverIso,
    restrictOverTrivialization_comp]

end Scheme.Modules

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenFrameTransitivity
