/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenRestrictionComposition
import OAI.AlgebraicGeometry.SheafCohomology.Projective.RestrictionPullbackComposition
import OAI.AlgebraicGeometry.SheafCohomology.Projective.RestrictionUnit

/-! # Open Pullback Frame -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenPullbackFrame

noncomputable section

open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules

/-! Pullback presentation of the actual restricted local frames. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory Opposite
universe u
section
open Scheme.Modules

theorem restrictionPullback_congr {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [IsOpenImmersion f] [IsOpenImmersion g] (h : f = g) (M : Y.Modules) :
    (restrictFunctorCongr h).hom.app M ≫ (restrictFunctorIsoPullback g).hom.app M =
    (restrictFunctorIsoPullback f).hom.app M ≫ (pullbackCongr h).hom.app M := by
  subst g
  have he : (restrictFunctorCongr (rfl : f = f)).hom.app M = 𝟙 _ := by
    apply _root_.SheafOfModules.hom_ext
    ext U x
    change M.presheaf.map (𝟙 (.op (f ''ᵁ U.unop))) x = x
    rw [M.presheaf.map_id]
    rfl
  rw [he]
  change 𝟙 _ ≫ (restrictFunctorIsoPullback f).hom.app M =
    (restrictFunctorIsoPullback f).hom.app M ≫ 𝟙 _
  simp

theorem restrictionPullback_comp_cancel {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
    (M : Z.Modules) :
    (restrictFunctorIsoPullback (f ≫ g)).hom.app M ≫
      (pullbackComp f g).inv.app M ≫
      (pullback f).map ((restrictFunctorIsoPullback g).inv.app M) =
    (restrictFunctorComp f g).hom.app M ≫
      (restrictFunctorIsoPullback f).hom.app ((restrictFunctor g).obj M) := by
  have h := NatTrans.congr_app (RestrictionPullbackComposition.restrictionPullback_composition f g) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  apply (cancel_mono ((pullback f).map ((restrictFunctorIsoPullback g).hom.app M))).1
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id]
  erw [Category.comp_id]
  have hn := (restrictFunctorIsoPullback f).hom.naturality
    ((restrictFunctorIsoPullback g).hom.app M)
  erw [← hn]
  apply (cancel_mono ((pullbackComp f g).hom.app M)).1
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  exact h.symm

theorem restrictionPullback_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] :
    (restrictFunctorIsoPullback f).hom.app (Invertible.Scheme.Modules.unitObj Y) ≫ (Invertible.Scheme.Modules.pullbackUnitIso f).hom =
      (restrictUnitIso f).hom := by
  rw [← RestrictionUnit.restrictFunctorIsoPullback_inv_comp_restrictUnitIso]
  exact Iso.hom_inv_id_assoc ((restrictFunctorIsoPullback f).app (Invertible.Scheme.Modules.unitObj Y)) _

end

namespace Scheme.Modules

def restrictOpenTrivializationPullback {X : Scheme.{u}} {M : X.Modules}
    {U V : X.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ Invertible.Scheme.Modules.unitObj U.toScheme) :
    M.restrict V.ι ≅ Invertible.Scheme.Modules.unitObj V.toScheme :=
  (restrictFunctorIsoPullback V.ι).app M ≪≫
    Invertible.Scheme.Modules.restrictTrivialization h ((restrictFunctorIsoPullback U.ι).symm.app M ≪≫ e)

theorem restrictOpenTrivialization_eq_pullback {X : Scheme.{u}} {M : X.Modules}
    {U V : X.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ Invertible.Scheme.Modules.unitObj U.toScheme) :
    OpenFrames.Scheme.Modules.restrictOpenTrivialization h e = restrictOpenTrivializationPullback h e := by
  rw [← OpenRestrictionComposition.nativeOpenFrame_eq_over]
  apply Iso.ext
  have hc := restrictionPullback_congr
    (X.homOfLE_ι h).symm M
  have hp := restrictionPullback_comp_cancel
    (X.homOfLE h) U.ι M
  have hn := (restrictFunctorIsoPullback (X.homOfLE h)).hom.naturality e.hom
  have hu := restrictionPullback_unit (X.homOfLE h)
  simp only [OpenRestrictionComposition.nativeOpenFrame,
    OpenRestrictionComposition.nestedRestrictionIso, restrictOpenTrivializationPullback,
    Invertible.Scheme.Modules.restrictTrivialization, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  slice_rhs 1 2 => erw [← hc]
  simp only [Category.assoc]
  slice_rhs 2 4 => erw [hp]
  simp only [Category.assoc]
  slice_rhs 3 4 => erw [← hn]
  simp only [Category.assoc]
  erw [hu]
  rfl

end Scheme.Modules

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenPullbackFrame
