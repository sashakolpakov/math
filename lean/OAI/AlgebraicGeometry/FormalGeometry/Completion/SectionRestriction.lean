import Mathlib.AlgebraicGeometry.Restrict

/-! # Section Restriction -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SectionRestriction.Construction

noncomputable section

/-! # Completion: restriction of an actual scheme section to a base open -/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) (U : Y.Opens)

include hs

/-- The section over a base open lands in its actual inverse-image open. -/
theorem schemeSectionRestrict_range : Set.range (U.ι ≫ s) ⊆ Set.range (f ⁻¹ᵁ U).ι := by
  have h : (U.ι ≫ s) ≫ f = U.ι := by rw [Category.assoc, hs, Category.comp_id]
  rintro _ ⟨u, rfl⟩
  rw [Scheme.Opens.range_ι]
  change f ((U.ι ≫ s) u) ∈ U
  rw [← Scheme.Hom.comp_apply, h]
  exact u.property

/-- The restriction of a scheme section to an arbitrary base open. -/
def schemeSectionRestrict : U.toScheme ⟶ (f ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift (f ⁻¹ᵁ U).ι (U.ι ≫ s) (schemeSectionRestrict_range f s hs U)

@[reassoc]
theorem schemeSectionRestrict_ι :
    schemeSectionRestrict f s hs U ≫ (f ⁻¹ᵁ U).ι = U.ι ≫ s :=
  IsOpenImmersion.lift_fac _ _ _

/-- The restricted morphism retains the actual section identity. -/
theorem schemeSectionRestrict_section :
    schemeSectionRestrict f s hs U ≫ (f ∣_ U) = 𝟙 U.toScheme := by
  rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι,
    ← Category.assoc, schemeSectionRestrict_ι, Category.assoc, hs,
    Category.comp_id, Category.id_comp]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SectionRestriction.Construction
