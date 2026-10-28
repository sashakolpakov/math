import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.ReturnEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SegreOver
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

/-! # Products -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective

noncomputable section

/-! Construct projective presentations of products over any base scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} {X Y X' Y' : Over S}

def ProjectivePresentations.ProjectivePresentation.ofSourceIso (P : ProjectivePresentations.ProjectivePresentation Y) (e : X ≅ Y) :
    ProjectivePresentations.ProjectivePresentation X where
  dimension := P.dimension
  embedding := e.hom ≫ P.embedding
  closedImmersion := @IsClosedImmersion.comp _ _ _ _ _ (Grassmann.ProjectivePresentation.overIso_closedImmersion e) P.closedImmersion

def Products.nativeSegreProductEmbedding (S : Scheme.{u}) (n m : ℕ) :
    ProjectivePresentations.projectiveSpaceOver S n ⊗ ProjectivePresentations.projectiveSpaceOver S m ⟶
      ProjectivePresentations.projectiveSpaceOver S (Affine.SegreOver.segreProjectiveDimension.{u} n m) :=
  Pullback.ReturnEmbedding.pullbackReturnEmbedding S.toSpecΓ
    (Affine.SegreOver.affineSegreStandardEmbedding Γ(S, ⊤) n m)
    (SpaceBaseChange.projectiveSpaceOverSpecIso Γ(S, ⊤) (Affine.SegreOver.segreProjectiveDimension.{u} n m)).inv
    (SpaceBaseChange.projectiveSpaceOverBaseChangeIso S.toSpecΓ (Affine.SegreOver.segreProjectiveDimension.{u} n m)).inv
    (Functor.Monoidal.μIso (Over.pullback S.toSpecΓ)
      (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n) (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) m)).hom

theorem Products.nativeSegreProductEmbedding_closed (S : Scheme.{u}) (n m : ℕ) :
    IsClosedImmersion (Products.nativeSegreProductEmbedding S n m).left := by
  exact @Pullback.ReturnEmbedding.pullbackReturnEmbedding_closed _ _ _ _ _ _ S.toSpecΓ
    (Affine.SegreOver.affineSegreStandardEmbedding Γ(S, ⊤) n m)
    (SpaceBaseChange.projectiveSpaceOverSpecIso Γ(S, ⊤) (Affine.SegreOver.segreProjectiveDimension.{u} n m)).inv
    (SpaceBaseChange.projectiveSpaceOverBaseChangeIso S.toSpecΓ (Affine.SegreOver.segreProjectiveDimension.{u} n m)).inv
    (Functor.Monoidal.μIso (Over.pullback S.toSpecΓ)
      (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n) (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) m)).hom
    (Affine.SegreOver.affineSegreStandardEmbedding_isClosedImmersion Γ(S, ⊤) n m)
    (Grassmann.ProjectivePresentation.overIso_closedImmersion (SpaceBaseChange.projectiveSpaceOverSpecIso
      Γ(S, ⊤) (Affine.SegreOver.segreProjectiveDimension.{u} n m)).symm)
    (Grassmann.ProjectivePresentation.overIso_closedImmersion (SpaceBaseChange.projectiveSpaceOverBaseChangeIso S.toSpecΓ
      (Affine.SegreOver.segreProjectiveDimension.{u} n m)).symm)
    (Grassmann.ProjectivePresentation.overIso_closedImmersion (Functor.Monoidal.μIso (Over.pullback S.toSpecΓ)
      (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n) (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) m)))

def Products.projectiveSpaceProductPresentation (S : Scheme.{u}) (n m : ℕ) :
    ProjectivePresentations.ProjectivePresentation (ProjectivePresentations.projectiveSpaceOver S n ⊗ ProjectivePresentations.projectiveSpaceOver S m) where
  dimension := Affine.SegreOver.segreProjectiveDimension.{u} n m
  embedding := Products.nativeSegreProductEmbedding S n m
  closedImmersion := Products.nativeSegreProductEmbedding_closed S n m

theorem Products.overTensorMap_closed (a : X ⟶ X') (b : Y ⟶ Y')
    [IsClosedImmersion a.left] [IsClosedImmersion b.left] :
    IsClosedImmersion (a ⊗ₘ b).left := by
  let : MorphismProperty.IsStableUnderComposition (@IsClosedImmersion : MorphismProperty Scheme.{u}) :=
    ⟨fun f g hf hg => @IsClosedImmersion.comp _ _ _ f g hf hg⟩
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    (f := X.hom) (g := Y.hom) (f' := X'.hom) (g' := Y'.hom)
    (i₁ := a.left) (i₂ := b.left) inferInstance inferInstance a.w.symm b.w.symm

def Products.projectiveProductEmbedding {S : Scheme.{u}} {X Y : Over S} {n m : ℕ}
    (i : X ⟶ ProjectivePresentations.projectiveSpaceOver S n) (j : Y ⟶ ProjectivePresentations.projectiveSpaceOver S m) :
    X ⊗ Y ⟶ ProjectivePresentations.projectiveSpaceOver S (Affine.SegreOver.segreProjectiveDimension.{u} n m) :=
  (i ⊗ₘ j) ≫ Products.nativeSegreProductEmbedding S n m

theorem Products.projectiveProductEmbedding_closed {S : Scheme.{u}} {X Y : Over S} {n m : ℕ}
    (i : X ⟶ ProjectivePresentations.projectiveSpaceOver S n) (j : Y ⟶ ProjectivePresentations.projectiveSpaceOver S m)
    [hi : IsClosedImmersion i.left] [hj : IsClosedImmersion j.left] :
    IsClosedImmersion (Products.projectiveProductEmbedding i j).left :=
  @IsClosedImmersion.comp _ _ _ _ _ (Products.overTensorMap_closed i j)
    (Products.nativeSegreProductEmbedding_closed S n m)

def ProjectivePresentations.ProjectivePresentation.product (P : ProjectivePresentations.ProjectivePresentation X) (Q : ProjectivePresentations.ProjectivePresentation Y) :
    ProjectivePresentations.ProjectivePresentation (X ⊗ Y) where
  dimension := Affine.SegreOver.segreProjectiveDimension.{u} P.dimension Q.dimension
  embedding := Products.projectiveProductEmbedding P.embedding Q.embedding
  closedImmersion := Products.projectiveProductEmbedding_closed P.embedding Q.embedding

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective
