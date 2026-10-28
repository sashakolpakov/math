import OAI.AlgebraicGeometry.Resolution.Blowups.ProtectedProjectiveEmbedding
import OAI.AlgebraicGeometry.Resolution.Blowups.ProjectiveStrictTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.BaseCases
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ProjectiveSmoothTo

/-! # Strong -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Strong.Construction

noncomputable section

/-! Strong resolution of the frozen integral projective complex variety statement, with no restriction on dimension or codimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem resolution_of_singularities
    (X : Scheme) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X]
    (P : Foundations.Scheme.SmoothProjective.ProjectivePresentation X f) :
    letI : LocallyOfFinitePresentation f := P.locallyOfFinitePresentation
    ∃ (R : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : R.carrier ⟶ X),
      π ≫ f = R.structureMap ∧ IsProper π ∧
      (∃ e : R.carrier.PartialIso X,
        e.source.ι ≫ π = e.iso.hom ≫ e.target.ι) ∧
      IsIso (π ∣_ f.smoothLocus) := by
  let : LocallyOfFinitePresentation f := P.locallyOfFinitePresentation
  let : AlgebraicGeometry.IsNoetherian X := P.isNoetherian
  let : IsClosedImmersion P.embedding := P.closedImmersion
  let : Smooth (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase P.ambientDimension) :=
    ComplexGroups.HolomorphicAlgebraicity.ProjectiveSmoothTo.Constructions.ProjectiveSmooth.smooth_projectiveSpaceToBase P.ambientDimension
  by_cases hker : P.embedding.ker = ⊥
  · let : IsIso P.embedding := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
    let : Smooth f := P.over_base ▸ inferInstanceAs
      (Smooth (P.embedding ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase P.ambientDimension))
    exact BaseCases.Construction.resolution_of_singularities_of_smooth X f P
  · let : IsIntegral (Foundations.Scheme.ProjectiveSpace.projectiveSpace P.ambientDimension) :=
      ComplexGroups.HolomorphicAlgebraicity.ProjectiveSmoothTo.Constructions.ProjectiveSmooth.isIntegral_projectiveSpace P.ambientDimension
    let O := AmbientOpenExtension.Construction.projectiveSmoothAmbientOpen f P
    let : Nonempty (P.embedding ⁻¹ᵁ O).toScheme := ProjectiveStrictTransform.Construction.projectiveSmoothAmbientOpen_nonempty f P
    let : Smooth ((P.embedding ⁻¹ᵁ O).ι ≫ (P.embedding ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase P.ambientDimension)) := by
      rw [P.over_base]
      change Smooth ((P.embedding ⁻¹ᵁ AmbientOpenExtension.Construction.projectiveSmoothAmbientOpen f P).ι ≫ f)
      rw [AmbientOpenExtension.Construction.projectiveSmoothAmbientOpen_preimage]
      exact ResolutionGeometry.Construction.smooth_on_smoothLocus X f P
    obtain ⟨Y, p, ⟨Q⟩, hp, hO, hsm⟩ := ProtectedProjectiveEmbedding.Construction.exists_projective_smooth_embeddedStrictTransform
      (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase P.ambientDimension) (GlobalBlowup.Projectivity.Construction.identityProjectivePresentation P.ambientDimension)
      P.embedding hker O
    let : IsProper p := hp
    let : IsIso (p ∣_ O) := hO
    have hover : (EmbeddedStrictTransform.Construction.embeddedStrictOpenMap p P.embedding O).imageι ≫
        (p ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase P.ambientDimension) = ProjectiveStrictTransform.Construction.projectiveStrictToBase f P p ≫ f := by
      rw [← Category.assoc, ← EmbeddedStrictTransform.Construction.embeddedStrictToBase_over, Category.assoc, P.over_base]
      rfl
    let : Smooth (ProjectiveStrictTransform.Construction.projectiveStrictToBase f P p ≫ f) := hover ▸ hsm
    let : IsIntegral (ProjectiveStrictTransform.Construction.projectiveStrictTransform f P p) := ProjectiveStrictTransform.Construction.projectiveStrictTransform_isIntegral f P p
    let R : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety :=
      ⟨{ carrier := ProjectiveStrictTransform.Construction.projectiveStrictTransform f P p
         structureMap := ProjectiveStrictTransform.Construction.projectiveStrictToBase f P p ≫ f
         projective := ProjectiveStrictTransform.Construction.projectiveStrictTransformPresentation f P p Q
         smooth := inferInstance }, inferInstance⟩
    exact ⟨R, ProjectiveStrictTransform.Construction.projectiveStrictToBase f P p, rfl, ProjectiveStrictTransform.Construction.projectiveStrictToBase_isProper f P p,
      ProjectiveStrictTransform.Construction.projectiveStrictToBase_partialIso f P p, ProjectiveStrictTransform.Construction.projectiveStrictToBase_smoothLocus_isIso f P p⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Strong.Construction
