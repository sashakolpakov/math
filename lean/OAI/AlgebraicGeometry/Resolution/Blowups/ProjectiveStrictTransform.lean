import OAI.AlgebraicGeometry.Resolution.Blowups.EmbeddedStrictTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.AmbientOpenExtension

/-! # Projective Strict Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ProjectiveStrictTransform.Construction

noncomputable section

/-! Actual projective strict transforms with an isomorphism over the whole original smooth locus.
This file proves their geometric properties; it does not assert terminal smoothness.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem projectiveSmoothAmbientOpen_nonempty {Z : Scheme} (f : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsIntegral Z] (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation Z f) :
    Nonempty (P.embedding ⁻¹ᵁ AmbientOpenExtension.Construction.projectiveSmoothAmbientOpen f P).toScheme := by
  let : LocallyOfFinitePresentation f := P.locallyOfFinitePresentation
  rw [AmbientOpenExtension.Construction.projectiveSmoothAmbientOpen_preimage]
  obtain ⟨x, hx⟩ := (ResolutionGeometry.Construction.smoothLocus_dense Z f P).nonempty
  exact ⟨⟨x, hx⟩⟩

abbrev projectiveStrictTransform {Z Y : Scheme} (f : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation Z f) (π : Y ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace P.ambientDimension)
    [IsIso (π ∣_ AmbientOpenExtension.Construction.projectiveSmoothAmbientOpen f P)] : Scheme :=
  EmbeddedStrictTransform.Construction.embeddedStrictTransform π P.embedding (AmbientOpenExtension.Construction.projectiveSmoothAmbientOpen f P)

def projectiveStrictToBase {Z Y : Scheme} (f : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation Z f) (π : Y ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace P.ambientDimension)
    [IsIso (π ∣_ AmbientOpenExtension.Construction.projectiveSmoothAmbientOpen f P)] : projectiveStrictTransform f P π ⟶ Z := by
  let : IsClosedImmersion P.embedding := P.closedImmersion
  exact EmbeddedStrictTransform.Construction.embeddedStrictToBase π P.embedding (AmbientOpenExtension.Construction.projectiveSmoothAmbientOpen f P)

theorem projectiveStrictTransform_isIntegral {Z Y : Scheme} (f : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsIntegral Z] (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation Z f) (π : Y ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace P.ambientDimension)
    [IsIso (π ∣_ AmbientOpenExtension.Construction.projectiveSmoothAmbientOpen f P)] : IsIntegral (projectiveStrictTransform f P π) := by
  let : AlgebraicGeometry.IsNoetherian Z := P.isNoetherian
  let : Nonempty (P.embedding ⁻¹ᵁ AmbientOpenExtension.Construction.projectiveSmoothAmbientOpen f P).toScheme :=
    projectiveSmoothAmbientOpen_nonempty f P
  exact EmbeddedStrictTransform.Construction.embeddedStrictTransform_isIntegral π P.embedding (AmbientOpenExtension.Construction.projectiveSmoothAmbientOpen f P)

theorem projectiveStrictToBase_isProper {Z Y : Scheme} (f : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation Z f) (π : Y ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace P.ambientDimension)
    [IsProper π] [IsIso (π ∣_ AmbientOpenExtension.Construction.projectiveSmoothAmbientOpen f P)] :
    IsProper (projectiveStrictToBase f P π) := by
  let : IsClosedImmersion P.embedding := P.closedImmersion
  exact EmbeddedStrictTransform.Construction.embeddedStrictToBase_isProper π P.embedding (AmbientOpenExtension.Construction.projectiveSmoothAmbientOpen f P)

theorem projectiveStrictToBase_smoothLocus_isIso {Z Y : Scheme} (f : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation Z f) (π : Y ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace P.ambientDimension)
    [IsIso (π ∣_ AmbientOpenExtension.Construction.projectiveSmoothAmbientOpen f P)] :
    letI : LocallyOfFinitePresentation f := P.locallyOfFinitePresentation
    IsIso (projectiveStrictToBase f P π ∣_ f.smoothLocus) := by
  let : LocallyOfFinitePresentation f := P.locallyOfFinitePresentation
  let : IsClosedImmersion P.embedding := P.closedImmersion
  let : AlgebraicGeometry.IsNoetherian Z := P.isNoetherian
  have h := EmbeddedStrictTransform.Construction.embeddedStrictToBase_restrict_isIso π P.embedding (AmbientOpenExtension.Construction.projectiveSmoothAmbientOpen f P)
  rwa [AmbientOpenExtension.Construction.projectiveSmoothAmbientOpen_preimage] at h

theorem projectiveStrictToBase_partialIso {Z Y : Scheme} (f : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    [IsIntegral Z] (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation Z f) (π : Y ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace P.ambientDimension)
    [IsIso (π ∣_ AmbientOpenExtension.Construction.projectiveSmoothAmbientOpen f P)] :
    ∃ e : (projectiveStrictTransform f P π).PartialIso Z,
      e.source.ι ≫ projectiveStrictToBase f P π = e.iso.hom ≫ e.target.ι := by
  let : IsClosedImmersion P.embedding := P.closedImmersion
  let : AlgebraicGeometry.IsNoetherian Z := P.isNoetherian
  let : Nonempty (P.embedding ⁻¹ᵁ AmbientOpenExtension.Construction.projectiveSmoothAmbientOpen f P).toScheme :=
    projectiveSmoothAmbientOpen_nonempty f P
  exact EmbeddedStrictTransform.Construction.embeddedStrictToBase_partialIso π P.embedding (AmbientOpenExtension.Construction.projectiveSmoothAmbientOpen f P)

def projectiveStrictTransformPresentation {Z Y : Scheme} (f : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation Z f) (π : Y ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace P.ambientDimension)
    [IsIso (π ∣_ AmbientOpenExtension.Construction.projectiveSmoothAmbientOpen f P)]
    (Q : Foundations.Scheme.SmoothProjective.ProjectivePresentation Y (π ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase P.ambientDimension)) :
    Foundations.Scheme.SmoothProjective.ProjectivePresentation (projectiveStrictTransform f P π) (projectiveStrictToBase f P π ≫ f) := by
  let : IsClosedImmersion P.embedding := P.closedImmersion
  have he : (EmbeddedStrictTransform.Construction.embeddedStrictOpenMap π P.embedding (AmbientOpenExtension.Construction.projectiveSmoothAmbientOpen f P)).imageι ≫
      (π ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase P.ambientDimension) = projectiveStrictToBase f P π ≫ f := by
    rw [← Category.assoc, ← EmbeddedStrictTransform.Construction.embeddedStrictToBase_over, Category.assoc, P.over_base]
    rfl
  exact he ▸ EmbeddedStrictTransform.Construction.embeddedStrictTransformProjectivePresentation π P.embedding (AmbientOpenExtension.Construction.projectiveSmoothAmbientOpen f P) Q

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ProjectiveStrictTransform.Construction
