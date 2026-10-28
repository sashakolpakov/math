import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.SectionFunctions
import OAI.AlgebraicGeometry.FormalGeometry.Completion.SectionRestriction

/-! # Integral Section Iso -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralSectionIso.Construction

noncomputable section

/-!
# Completion: integral morphisms from integral schemes with a section

The split integral algebra argument applies on every nonempty affine base
open. It proves that an integral morphism from an integral scheme is an
isomorphism whenever it has a section.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X]
  (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y)

include s hs

/-- An integral morphism from an integral scheme with an actual section is an isomorphism. -/
theorem integralMorphism_section_isIso [IsIntegralHom f] : IsIso f := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme)
  intro y
  obtain ⟨_, ⟨U₀, hU, rfl⟩, hy, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  let U : Y.Opens := U₀
  have : Nonempty U.toScheme := ⟨⟨y, hy⟩⟩
  have : Nonempty (f ⁻¹ᵁ U).toScheme :=
    Nonempty.map (SectionRestriction.Construction.schemeSectionRestrict f s hs U) inferInstance
  have : IsIntegral (f ⁻¹ᵁ U).toScheme := isIntegral_of_isOpenImmersion (f ⁻¹ᵁ U).ι
  have : IsAffine U.toScheme := hU
  have : IsAffine (f ⁻¹ᵁ U).toScheme := isAffine_of_isAffineHom (f ∣_ U)
  have := Proper.SectionFunctions.Construction.integralFamily_section_appTop_isIso (f ∣_ U)
    (SectionRestriction.Construction.schemeSectionRestrict f s hs U) (SectionRestriction.Construction.schemeSectionRestrict_section f s hs U)
  refine ⟨U, hy, ?_⟩
  apply (HasAffineProperty.iff_of_isAffine (P := MorphismProperty.isomorphisms Scheme)).mpr
  exact ⟨inferInstance, inferInstance⟩

/-- The relative normalization of an integral proper family with a section is the entire base. -/
theorem integralProperFamily_section_fromNormalization_isIso [IsProper f] :
    IsIso f.fromNormalization := by
  apply integralMorphism_section_isIso f.fromNormalization (s ≫ f.toNormalization)
  rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization, hs]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.IntegralSectionIso.Construction
