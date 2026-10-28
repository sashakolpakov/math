import OAI.CategoryTheory.Functors.FunctorReturnIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Grassmann.ProjectivePresentation

/-! # Presentation Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective

noncomputable section

/-! Actual projective presentations are preserved by arbitrary scheme base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- The standard affine presentation with its coefficient ring kept bundled. -/
def PresentationBaseChange.nativeAffineProjectivePresentation (R : CommRingCat.{u}) (n : ℕ) :
    ProjectivePresentations.ProjectivePresentation (S := Spec R) (ProjectivePresentations.affineProjectiveSpace R n) where
  dimension := n
  embedding := (SpaceBaseChange.projectiveSpaceOverSpecIso R n).inv
  closedImmersion := Grassmann.ProjectivePresentation.overIso_closedImmersion (SpaceBaseChange.projectiveSpaceOverSpecIso R n).symm

instance PresentationBaseChange.nativeAffineProjectivePresentation_embedding_isIso (R : CommRingCat.{u}) (n : ℕ) :
    IsIso (PresentationBaseChange.nativeAffineProjectivePresentation R n).embedding :=
  inferInstanceAs (IsIso (SpaceBaseChange.projectiveSpaceOverSpecIso R n).inv)

variable {S T : Scheme.{u}} {X Y : Over S}

theorem PresentationBaseChange.overPullback_map_isPullback (j : X ⟶ Y) (f : T ⟶ S) :
    IsPullback (pullback.fst X.hom f) ((Over.pullback f).map j).left
      j.left (pullback.fst Y.hom f) := by
  let b := (Over.pullback f).map j
  have hb : b.left ≫ pullback.snd Y.hom f = pullback.snd X.hom f := b.w
  have hj : j.left ≫ Y.hom = X.hom := j.w
  have houter : IsPullback (pullback.fst X.hom f)
      (b.left ≫ pullback.snd Y.hom f) (j.left ≫ Y.hom) f := by
    rw [hb, hj]
    exact IsPullback.of_hasPullback X.hom f
  have hc : pullback.fst X.hom f ≫ j.left = b.left ≫ pullback.fst Y.hom f := by
    change pullback.fst X.hom f ≫ j.left =
      pullback.lift (pullback.fst X.hom f ≫ j.left) (pullback.snd X.hom f) _ ≫
        pullback.fst Y.hom f
    exact (pullback.lift_fst _ _ _).symm
  exact houter.of_bot hc (IsPullback.of_hasPullback Y.hom f)

theorem PresentationBaseChange.overPullback_map_closed (j : X ⟶ Y) [IsClosedImmersion j.left] (f : T ⟶ S) :
    IsClosedImmersion ((Over.pullback f).map j).left :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (PresentationBaseChange.overPullback_map_isPullback j f) inferInstance

def ProjectivePresentations.ProjectivePresentation.nativeBaseChangeEmbedding (P : ProjectivePresentations.ProjectivePresentation X) (f : T ⟶ S) :
    (Over.pullback f).obj X ⟶ ProjectivePresentations.projectiveSpaceOver T P.dimension :=
  CategoryTheory.Functors.FunctorReturnIsomorphism.functorReturnMap (Over.pullback f) P.embedding
    (SpaceBaseChange.projectiveSpaceOverBaseChangeIso f P.dimension)

theorem ProjectivePresentations.ProjectivePresentation.nativeBaseChangeEmbedding_closed (P : ProjectivePresentations.ProjectivePresentation X) (f : T ⟶ S) :
    IsClosedImmersion (P.nativeBaseChangeEmbedding f).left := by
    change IsClosedImmersion (((Over.pullback f).map P.embedding).left ≫
      (SpaceBaseChange.projectiveSpaceOverBaseChangeIso f P.dimension).inv.left)
    exact @IsClosedImmersion.comp _ _ _ _ _ (PresentationBaseChange.overPullback_map_closed P.embedding f)
      (Grassmann.ProjectivePresentation.overIso_closedImmersion (SpaceBaseChange.projectiveSpaceOverBaseChangeIso f P.dimension).symm)

abbrev ProjectivePresentations.ProjectivePresentation.baseChange (P : ProjectivePresentations.ProjectivePresentation X) (f : T ⟶ S) :
    ProjectivePresentations.ProjectivePresentation ((Over.pullback f).obj X) where
  dimension := P.dimension
  embedding := P.nativeBaseChangeEmbedding f
  closedImmersion := P.nativeBaseChangeEmbedding_closed f

/-- Base change of a presentation whose embedding is an isomorphism. -/
def ProjectivePresentations.ProjectivePresentation.baseChangeIso (P : ProjectivePresentations.ProjectivePresentation X)
    [IsIso P.embedding] (f : T ⟶ S) :
    (Over.pullback f).obj X ≅ ProjectivePresentations.projectiveSpaceOver T P.dimension :=
  CategoryTheory.Functors.FunctorReturnIsomorphism.functorReturnIso (Over.pullback f) (asIso P.embedding)
    (SpaceBaseChange.projectiveSpaceOverBaseChangeIso f P.dimension)

theorem ProjectivePresentations.ProjectivePresentation.baseChangeIso_hom (P : ProjectivePresentations.ProjectivePresentation X)
    [IsIso P.embedding] (f : T ⟶ S) :
    (P.baseChangeIso f).hom = P.nativeBaseChangeEmbedding f :=
  CategoryTheory.Functors.FunctorReturnIsomorphism.functorReturnIso_hom (Over.pullback f) (asIso P.embedding)
    (SpaceBaseChange.projectiveSpaceOverBaseChangeIso f P.dimension)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective
