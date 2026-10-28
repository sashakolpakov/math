import OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralSplitMap
import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.Normalization

/-! # Section Functions -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.SectionFunctions.Construction

noncomputable section

/-!
# Completion: global functions of integral proper families with a section

The section splits the integral map on global functions. Since the total
space is integral, this forces that map to be an isomorphism. Consequently
the actual relative normalization over an affine base is the base itself.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsAffine Y]
  (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y)

include s hs

/-- An integral universally closed family with a section has exactly the base's
global functions. -/
theorem integralFamily_section_appTop_isIso [UniversallyClosed f] : IsIso f.appTop := by
  have : Nontrivial Γ(Y, ⊤) := f.appTop.hom.domain_nontrivial
  apply (ConcreteCategory.isIso_iff_bijective f.appTop).mpr
  apply IntegralSplitMap.Construction.integral_split_bijective f.appTop.hom s.appTop.hom
    (isIntegral_appTop_of_universallyClosed f)
  have h : f.appTop ≫ s.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, hs, Scheme.Hom.id_appTop]
  exact congrArg CommRingCat.Hom.hom h

/-- The actual relative normalization of such a proper family is the affine base. -/
theorem integralProperFamily_section_normalization_isIso [IsProper f] :
    IsIso f.fromNormalization := by
  have := integralFamily_section_appTop_isIso f s hs
  exact Normalization.Construction.proper_fromNormalization_isIso_of_appTop f

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.SectionFunctions.Construction
