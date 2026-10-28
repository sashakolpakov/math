/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicTopology.Support.SectionRestrictionCone

/-! # Section Restriction Is -/

namespace OAI.AlgebraicTopology.Support.SectionRestrictionIs.TopCat.Sheaf

noncomputable section

open _root_.TopCat
open _root_.TopCat.Sheaf

/-!
# Supported-section kernels and open restriction cones

-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

variable (X : TopCat.{u})

variable (U V : Opens X) (K : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ)

/-- On an open contained in the excluded open, the supported-section group is
zero because its defining restriction map is an isomorphism. -/
theorem supportedOutsideSections_isZero_of_le (F : Sheaf AddCommGrpCat.{u} X)
    (hVU : V ≤ U) :
    IsZero (((DerivedSections.TopCat.Sheaf.sheafSectionsSupportedOutside X U).obj F).obj.obj (op V)) := by
  have he : U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion').obj V) = V := by
    rw [Opens.functor_map_eq_inf, inf_eq_left.mpr hVU]
  have hi : IsIso (U.isOpenEmbedding.isOpenMap.adjunction.counit.app V) := by
    rw [show U.isOpenEmbedding.isOpenMap.adjunction.counit.app V = eqToHom he from
      Subsingleton.elim _ _]
    infer_instance
  let r := ((DerivedSections.TopCat.Sheaf.toOpenRestrictionPushforward X U).app F).hom.app (op V)
  have : IsIso r := by
    change IsIso (F.obj.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app V).op)
    infer_instance
  exact (isZero_kernel_of_mono r).of_iso (DerivedSectionsOn.TopCat.Sheaf.sheafSectionsSupportedOutsideOnOpenIso X U V F)

end

end OAI.AlgebraicTopology.Support.SectionRestrictionIs.TopCat.Sheaf
