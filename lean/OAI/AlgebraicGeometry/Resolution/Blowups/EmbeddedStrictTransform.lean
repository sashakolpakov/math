import OAI.AlgebraicGeometry.Resolution.Blowups.SchemeImageClosedLift
import OAI.AlgebraicGeometry.Resolution.Blowups.StrictTransform

/-! # Embedded Strict Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EmbeddedStrictTransform.Construction

noncomputable section

/-! Strict transforms of actual closed embeddings, retaining the original source scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

def embeddedStrictOpenMap {Z Y X : Scheme.{u}} (π : Y ⟶ X)
    (i : Z ⟶ X) (U : X.Opens) [IsIso (π ∣_ U)] : (i ⁻¹ᵁ U).toScheme ⟶ Y :=
  ((i ∣_ U) ≫ inv (π ∣_ U)) ≫ (π ⁻¹ᵁ U).ι

theorem embeddedStrictOpenMap_over {Z Y X : Scheme.{u}} (π : Y ⟶ X)
    (i : Z ⟶ X) (U : X.Opens) [IsIso (π ∣_ U)] :
    embeddedStrictOpenMap π i U ≫ π = (i ⁻¹ᵁ U).ι ≫ i := by
  simp only [embeddedStrictOpenMap, Category.assoc, ← morphismRestrict_ι,
    IsIso.inv_hom_id_assoc]

instance embeddedStrictOpenMap_isImmersion {Z Y X : Scheme.{u}} (π : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Opens) [IsIso (π ∣_ U)] :
    IsImmersion (embeddedStrictOpenMap π i U) := by
  unfold embeddedStrictOpenMap
  infer_instance

abbrev embeddedStrictTransform {Z Y X : Scheme.{u}} (π : Y ⟶ X)
    (i : Z ⟶ X) (U : X.Opens) [IsIso (π ∣_ U)] : Scheme.{u} :=
  (embeddedStrictOpenMap π i U).image

def embeddedStrictToBase {Z Y X : Scheme.{u}} (π : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Opens) [IsIso (π ∣_ U)] :
    embeddedStrictTransform π i U ⟶ Z :=
  SchemeImageClosedLift.Construction.schemeImageClosedLift (embeddedStrictOpenMap π i U) (i ⁻¹ᵁ U).ι π i
    (embeddedStrictOpenMap_over π i U)

theorem embeddedStrictToBase_over {Z Y X : Scheme.{u}} (π : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Opens) [IsIso (π ∣_ U)] :
    embeddedStrictToBase π i U ≫ i = (embeddedStrictOpenMap π i U).imageι ≫ π :=
  SchemeImageClosedLift.Construction.schemeImageClosedLift_over _ _ _ _ _

theorem embeddedStrictToBase_isProper {Z Y X : Scheme.{u}} (π : Y ⟶ X) [IsProper π]
    (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Opens) [IsIso (π ∣_ U)] :
    IsProper (embeddedStrictToBase π i U) :=
  SchemeImageClosedLift.Construction.schemeImageClosedLift_isProper _ _ _ _ _

theorem embeddedStrictTransform_isIntegral {Z Y X : Scheme.{u}} (π : Y ⟶ X)
    (i : Z ⟶ X) (U : X.Opens) [IsIso (π ∣_ U)] [NoetherianSpace Z] [IsIntegral Z]
    [Nonempty (i ⁻¹ᵁ U).toScheme] : IsIntegral (embeddedStrictTransform π i U) := by
  let : IsIntegral (i ⁻¹ᵁ U).toScheme := isIntegral_of_isOpenImmersion (i ⁻¹ᵁ U).ι
  exact Integral.SchemeImage.Construction.scheme_image_isIntegral (embeddedStrictOpenMap π i U)

theorem embeddedStrictOpenMap_toImage_over {Z Y X : Scheme.{u}} (π : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Opens) [IsIso (π ∣_ U)] :
    (embeddedStrictOpenMap π i U).toImage ≫ embeddedStrictToBase π i U = (i ⁻¹ᵁ U).ι :=
  SchemeImageClosedLift.Construction.schemeImageClosedLift_toImage _ _ _ _ _

theorem embeddedStrictOpenMap_toImage_opensRange {Z Y X : Scheme.{u}} (π : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Opens) [IsIso (π ∣_ U)] [NoetherianSpace Z] :
    (embeddedStrictOpenMap π i U).toImage.opensRange =
      embeddedStrictToBase π i U ⁻¹ᵁ (i ⁻¹ᵁ U) := by
  have he := Locally.ClosedImageRestriction.Construction.closed_open_image_opensRange ((i ∣_ U) ≫ inv (π ∣_ U)) (π ⁻¹ᵁ U).ι
  rw [Scheme.Opens.opensRange_ι] at he
  change (embeddedStrictOpenMap π i U).toImage.opensRange =
    (embeddedStrictOpenMap π i U).imageι ⁻¹ᵁ (π ⁻¹ᵁ U) at he
  rw [he]
  change ((embeddedStrictOpenMap π i U).imageι ≫ π) ⁻¹ᵁ U =
    (embeddedStrictToBase π i U ≫ i) ⁻¹ᵁ U
  rw [embeddedStrictToBase_over]

theorem embeddedStrictToBase_restrict_isIso {Z Y X : Scheme.{u}} (π : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Opens) [IsIso (π ∣_ U)] [NoetherianSpace Z] :
    IsIso (embeddedStrictToBase π i U ∣_ (i ⁻¹ᵁ U)) :=
  Open.InverseRestriction.Construction.isIso_restrict_of_open_inverse _ _ (embeddedStrictOpenMap π i U).toImage
    (embeddedStrictOpenMap_toImage_over π i U) (embeddedStrictOpenMap_toImage_opensRange π i U)

theorem embeddedStrictToBase_partialIso {Z Y X : Scheme} (π : Y ⟶ X)
    (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Opens) [IsIso (π ∣_ U)]
    [NoetherianSpace Z] [IsIntegral Z] [Nonempty (i ⁻¹ᵁ U).toScheme] :
    ∃ e : (embeddedStrictTransform π i U).PartialIso Z,
      e.source.ι ≫ embeddedStrictToBase π i U = e.iso.hom ≫ e.target.ι := by
  let : IsIntegral (embeddedStrictTransform π i U) := embeddedStrictTransform_isIntegral π i U
  let : IsIso (embeddedStrictToBase π i U ∣_ (i ⁻¹ᵁ U)) := embeddedStrictToBase_restrict_isIso π i U
  apply ResolutionGeometry.Construction.partialIso_of_isIso_restriction (embeddedStrictToBase π i U) (i ⁻¹ᵁ U)
  exact (i ⁻¹ᵁ U).isOpen.dense (by
    obtain ⟨x⟩ := ‹Nonempty (i ⁻¹ᵁ U).toScheme›
    exact ⟨x.1, x.2⟩)

def embeddedStrictTransformProjectivePresentation {Z Y X : Scheme} (π : Y ⟶ X)
    (i : Z ⟶ X) (U : X.Opens) [IsIso (π ∣_ U)]
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation Y g) :
    Foundations.Scheme.SmoothProjective.ProjectivePresentation (embeddedStrictTransform π i U) ((embeddedStrictOpenMap π i U).imageι ≫ g) :=
  ClosedTransformProjectivity.Construction.closedSubschemeProjectivePresentation P (embeddedStrictOpenMap π i U).ker

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EmbeddedStrictTransform.Construction
