/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.FrameSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OverGenerator

/-! # Open Frames -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenFrames

noncomputable section

open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules

/-! Restriction of rank-one frames and compatibility of their scalar maps. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory Opposite
universe u
section

theorem restrictTrivializationOfOverTrivializationOfRestrictIso
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.restrict U.ι ≅ Invertible.Scheme.Modules.unitObj U.toScheme) :
    FrameSections.restrictTrivializationOfOverIso M U
      (Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e) = e := by
  apply Iso.ext
  simp only [FrameSections.restrictTrivializationOfOverIso,
    Invertible.Scheme.Modules.overTrivializationOfRestrictIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.FullyFaithful.preimageIso_hom, Functor.FullyFaithful.map_preimage,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact ((Scheme.Modules.overFunctorEquiv U).app M).inv_hom_id_assoc e.hom

theorem overTrivializationOfRestrictTrivializationOfOverIso
    {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (e : M.over U ≅ _root_.SheafOfModules.unit (X.ringCatSheaf.over U)) :
    Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U
      (FrameSections.restrictTrivializationOfOverIso M U e) = e := by
  apply Iso.ext
  apply (Scheme.Modules.overEquiv U).functor.map_injective
  simp only [Invertible.Scheme.Modules.overTrivializationOfRestrictIso,
    FrameSections.restrictTrivializationOfOverIso, Functor.FullyFaithful.preimageIso_hom,
    Functor.FullyFaithful.map_preimage, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  exact ((Scheme.Modules.overFunctorEquiv U).app M).hom_inv_id_assoc
    ((Scheme.Modules.overEquiv U).functor.map e.hom)

end

namespace Scheme.Modules

def openTopSection {X : Scheme.{u}} (U : X.Opens) (r : Γ(X, U)) :
    Γ(U.toScheme, ⊤) := U.topIso.inv r

/-- Restriction through the equivalent over-site, with the canonical unit frame. -/
def restrictOpenTrivialization {X : Scheme.{u}} {M : X.Modules}
    {U V : X.Opens} (hVU : V ≤ U)
    (e : M.restrict U.ι ≅ Invertible.Scheme.Modules.unitObj U.toScheme) :
    M.restrict V.ι ≅ Invertible.Scheme.Modules.unitObj V.toScheme :=
  FrameSections.restrictTrivializationOfOverIso M V
    (Dual.SheafOfModules.restrictOverTrivialization
      X.ringCatSheaf M U (Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e)
      (Over.mk (homOfLE hVU)))

theorem overTrivializationOfRestrictOpenTrivialization {X : Scheme.{u}}
    {M : X.Modules} {U V : X.Opens} (hVU : V ≤ U)
    (e : M.restrict U.ι ≅ Invertible.Scheme.Modules.unitObj U.toScheme) :
    Invertible.Scheme.Modules.overTrivializationOfRestrictIso M V (restrictOpenTrivialization hVU e) =
      Dual.SheafOfModules.restrictOverTrivialization
        X.ringCatSheaf M U (Invertible.Scheme.Modules.overTrivializationOfRestrictIso M U e)
        (Over.mk (homOfLE hVU)) :=
  overTrivializationOfRestrictTrivializationOfOverIso M V _

end Scheme.Modules

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenFrames
