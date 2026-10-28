import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-! # Unramified Sections -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.UnramifiedSections.Construction

noncomputable section

/-! # Completion: unramifiedness of actual proper global functions from normalization -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

/-- The actual global section map inherits formal unramifiedness from the integral factor. -/
theorem proper_appTop_formallyUnramified {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [IsProper f] [FormallyUnramified f.fromNormalization] :
    f.appTop.hom.FormallyUnramified := by
  have : IsAffine f.normalization := isAffine_of_isAffineHom f.fromNormalization
  have : IsIso f.toNormalization.appTop := Normalization.Construction.proper_toNormalization_appTop_isIso f
  have hg : f.fromNormalization.appTop.hom.FormallyUnramified :=
    HasRingHomProperty.appTop (P := @FormallyUnramified) _ inferInstance
  have hh : f.toNormalization.appTop.hom.FormallyUnramified :=
    RingHom.FormallyUnramified.of_surjective
      (ConcreteCategory.bijective_of_isIso f.toNormalization.appTop).surjective
  have he : f.appTop = f.fromNormalization.appTop ≫ f.toNormalization.appTop := by
    rw [← Scheme.Hom.comp_appTop, Scheme.Hom.toNormalization_fromNormalization]
  rw [he, CommRingCat.hom_comp]
  exact hg.comp hh

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.UnramifiedSections.Construction
