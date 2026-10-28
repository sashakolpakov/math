import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.PullbackSectionCompatibility
import Mathlib.AlgebraicGeometry.Restrict

/-! # Section Restriction -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionRestriction.Construction

noncomputable section

/-! Restricting a section to a base open, with its induced isomorphism on global functions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (π : X ⟶ S) (s : S ⟶ X) (hs : s ≫ π = 𝟙 S)

include hs in
theorem section_preimage_le (U : S.Opens) : U ≤ s ⁻¹ᵁ (π ⁻¹ᵁ U) := by
  intro x hx
  have he : π (s x) = x := congrArg (fun f : S ⟶ S ↦ f x) hs
  exact (congrArg (fun y : S ↦ y ∈ U) he).mpr hx

def sectionRestrict (U : S.Opens) : U.toScheme ⟶ (π ⁻¹ᵁ U).toScheme :=
  IsOpenImmersion.lift (π ⁻¹ᵁ U).ι (U.ι ≫ s) (by
    rintro x ⟨y, rfl⟩
    exact ⟨⟨s y.val, section_preimage_le π s hs U y.property⟩, rfl⟩)

theorem sectionRestrict_ι (U : S.Opens) :
    sectionRestrict π s hs U ≫ (π ⁻¹ᵁ U).ι = U.ι ≫ s :=
  IsOpenImmersion.lift_fac _ _ _

theorem sectionRestrict_over (U : S.Opens) :
    sectionRestrict π s hs U ≫ (π ∣_ U) = 𝟙 U.toScheme := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, sectionRestrict_ι,
    Category.assoc, hs, Category.comp_id, Category.id_comp]

theorem isIso_restrict_appTop (hf : ∀ U : S.Opens, IsIso (π.app U)) (U : S.Opens) :
    IsIso (π ∣_ U).appTop := by
  have : IsIso (π.app (U.ι ''ᵁ ⊤)) := hf _
  let e := asIso (π.app (U.ι ''ᵁ ⊤)) ≪≫
    X.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage π U ⊤)).op
  exact (morphismRestrict_appTop π U).symm ▸ e.isIso_hom

theorem isIso_sectionRestrict_appTop (hf : ∀ U : S.Opens, IsIso (π.app U)) (U : S.Opens) :
    IsIso (sectionRestrict π s hs U).appTop := by
  have : IsIso (π ∣_ U).appTop := isIso_restrict_appTop π hf U
  have hc : (π ∣_ U).appTop ≫ (sectionRestrict π s hs U).appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, sectionRestrict_over, Scheme.Hom.id_appTop]
  have : IsIso ((π ∣_ U).appTop ≫ (sectionRestrict π s hs U).appTop) := hc.symm ▸ inferInstance
  exact IsIso.of_isIso_comp_left (π ∣_ U).appTop _

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SectionRestriction.Construction
