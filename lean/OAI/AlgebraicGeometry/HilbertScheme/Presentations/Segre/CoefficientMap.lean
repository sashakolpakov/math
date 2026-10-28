import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.SegrePresentation

/-! # Coefficient Map -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.CoefficientMap.Core

noncomputable section

/-! The coefficient map of the relative Segre presentation is the
affine Segre map applied to the two original coefficient maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u
variable {S : Scheme.{u}} {X Y : Over S}
variable (BX : Has.Core.ProjectivePresentation X) (BY : Has.Core.ProjectivePresentation Y)

def segrePairCoefficientMap : (X ⨯ Y).left ⟶
    (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) BX.dimension ⊗
      AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) BY.dimension).left :=
  ((OverProductTensorComparison.overProductTensorIso X Y).hom ≫ (BX.toHilbertConstruction.embedding ⊗ₘ BY.toHilbertConstruction.embedding)).left ≫
    (Functor.Monoidal.μIso (Over.pullback S.toSpecΓ)
      (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) BX.dimension)
      (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) BY.dimension)).hom.left ≫
        pullback.fst _ S.toSpecΓ

theorem segreProductPresentation_coefficientEmbedding :
    (Relative.SegrePresentation.Core.segreProductPresentation BX BY).coefficientEmbedding =
      segrePairCoefficientMap BX BY ≫
        (AbelianModuli.HilbertConstruction.Affine.SegreOver.affineSegreStandardEmbedding Γ(S, ⊤) BX.dimension BY.dimension).left := by
  let a : X ⨯ Y ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S BX.dimension ⊗
      AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S BY.dimension :=
    (OverProductTensorComparison.overProductTensorIso X Y).hom ≫ (BX.toHilbertConstruction.embedding ⊗ₘ BY.toHilbertConstruction.embedding)
  let e : (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S BX.dimension ⊗
      AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S BY.dimension) ≅
      (Over.pullback S.toSpecΓ).obj (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) BX.dimension ⊗
        AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) BY.dimension) := Functor.Monoidal.μIso (Over.pullback S.toSpecΓ)
    (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) BX.dimension)
    (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) BY.dimension)
  let k := AbelianModuli.HilbertConstruction.Affine.SegreOver.affineSegreStandardEmbedding Γ(S, ⊤) BX.dimension BY.dimension
  let r := Hilbert.ConstructionProjectivePresentationComparison.Core.e33ProjectiveSpaceIso S (AbelianModuli.HilbertConstruction.Affine.SegreOver.segreProjectiveDimension.{u} BX.dimension BY.dimension)
  let l : (Over.pullback S.toSpecΓ).obj
      (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) BX.dimension ⊗
        AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) BY.dimension) ⟶
      AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S (AbelianModuli.HilbertConstruction.Affine.SegreOver.segreProjectiveDimension.{u} BX.dimension BY.dimension) :=
    (Over.pullback S.toSpecΓ).map k
  let pD : (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S
      (AbelianModuli.HilbertConstruction.Affine.SegreOver.segreProjectiveDimension.{u} BX.dimension BY.dimension)).left ⟶ _ :=
    pullback.fst _ S.toSpecΓ
  let pA : ((Over.pullback S.toSpecΓ).obj
      (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) BX.dimension ⊗
        AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) BY.dimension)).left ⟶ _ :=
    pullback.fst _ S.toSpecΓ
  let qD : (Over.mk (Has.Core.projectiveSpaceProjection S
      (AbelianModuli.HilbertConstruction.Affine.SegreOver.segreProjectiveDimension.{u} BX.dimension BY.dimension))).left ⟶
      (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤)
        (AbelianModuli.HilbertConstruction.Affine.SegreOver.segreProjectiveDimension.{u} BX.dimension BY.dimension)).left :=
    pullback.fst _ S.toSpecΓ
  have hr : r.hom.left ≫ qD = pD :=
    Hilbert.ConstructionProjectivePresentationComparison.Core.e33ProjectiveSpaceIso_hom_fst S _
  have hl : l.left ≫ pD = pA ≫ k.left := pullback.lift_fst _ _ _
  change (((a.left ≫ e.hom.left ≫ l.left) ≫ r.hom.left) ≫ qD) =
    (a.left ≫ e.hom.left ≫ pA) ≫ k.left
  simp only [Category.assoc]
  rw [hr, hl]

theorem toHilbertConstruction_embedding_coefficient_fst :
    BX.toHilbertConstruction.embedding.left ≫
      pullback.fst (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) BX.dimension).hom S.toSpecΓ =
        BX.coefficientEmbedding := by
  exact (Category.assoc BX.embedding (Hilbert.ConstructionProjectivePresentationComparison.Core.e33ProjectiveSpaceIso S BX.dimension).inv.left
    (pullback.fst (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) BX.dimension).hom S.toSpecΓ)).trans
    (congrArg (fun k => BX.embedding ≫ k) (Hilbert.ConstructionProjectivePresentationComparison.Core.e33ProjectiveSpaceIso_inv_fst S BX.dimension))

theorem segrePairCoefficientMap_fst :
    segrePairCoefficientMap BX BY ≫
      (CartesianMonoidalCategory.fst
        (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) BX.dimension)
        (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) BY.dimension)).left =
      (prod.fst : X ⨯ Y ⟶ X).left ≫ BX.coefficientEmbedding := by
  let bx : X ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S BX.dimension := BX.toHilbertConstruction.embedding
  let byy : Y ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S BY.dimension := BY.toHilbertConstruction.embedding
  let a : X ⨯ Y ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S BX.dimension ⊗
      AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S BY.dimension :=
    (OverProductTensorComparison.overProductTensorIso X Y).hom ≫ (bx ⊗ₘ byy)
  let P := AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) BX.dimension
  let Q := AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) BY.dimension
  let e : (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S BX.dimension ⊗
      AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S BY.dimension) ≅ (Over.pullback S.toSpecΓ).obj (P ⊗ Q) :=
    Functor.Monoidal.μIso (Over.pullback S.toSpecΓ) P Q
  let pA : ((Over.pullback S.toSpecΓ).obj (P ⊗ Q)).left ⟶ (P ⊗ Q).left :=
    pullback.fst _ S.toSpecΓ
  let c := CartesianMonoidalCategory.fst P Q
  let cr := CartesianMonoidalCategory.fst
    (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S BX.dimension)
    (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S BY.dimension)
  let pX : (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S BX.dimension).left ⟶ _ :=
    pullback.fst _ S.toSpecΓ
  have he : e.hom.left ≫ pA ≫ c.left = cr.left ≫ pX :=
    Over.μ_pullback_left_fst_fst P Q
  have ha : a ≫ cr = prod.fst ≫ bx := by
    dsimp only [a, cr]
    rw [Category.assoc, CartesianMonoidalCategory.tensorHom_fst, ← Category.assoc,
      OverProductTensorComparison.overProductTensorIso_hom_fst]
  have hal : a.left ≫ cr.left = (prod.fst : X ⨯ Y ⟶ X).left ≫
      bx.left := congrArg Over.Hom.left ha
  have hc : bx.left ≫ pX = BX.coefficientEmbedding :=
    toHilbertConstruction_embedding_coefficient_fst BX
  change (a.left ≫ e.hom.left ≫ pA) ≫ c.left = _
  rw [Category.assoc, Category.assoc, he, ← Category.assoc, hal, Category.assoc, hc]
  rfl

theorem segrePairCoefficientMap_snd :
    segrePairCoefficientMap BX BY ≫
      (CartesianMonoidalCategory.snd
        (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) BX.dimension)
        (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) BY.dimension)).left =
      (prod.snd : X ⨯ Y ⟶ Y).left ≫ BY.coefficientEmbedding := by
  let bx : X ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S BX.dimension := BX.toHilbertConstruction.embedding
  let byy : Y ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S BY.dimension := BY.toHilbertConstruction.embedding
  let a : X ⨯ Y ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S BX.dimension ⊗
      AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S BY.dimension :=
    (OverProductTensorComparison.overProductTensorIso X Y).hom ≫ (bx ⊗ₘ byy)
  let P := AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) BX.dimension
  let Q := AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) BY.dimension
  let e : (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S BX.dimension ⊗
      AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S BY.dimension) ≅ (Over.pullback S.toSpecΓ).obj (P ⊗ Q) :=
    Functor.Monoidal.μIso (Over.pullback S.toSpecΓ) P Q
  let pA : ((Over.pullback S.toSpecΓ).obj (P ⊗ Q)).left ⟶ (P ⊗ Q).left :=
    pullback.fst _ S.toSpecΓ
  let c := CartesianMonoidalCategory.snd P Q
  let cr := CartesianMonoidalCategory.snd
    (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S BX.dimension)
    (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S BY.dimension)
  let pX : (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S BY.dimension).left ⟶ _ :=
    pullback.fst _ S.toSpecΓ
  have he : e.hom.left ≫ pA ≫ c.left = cr.left ≫ pX :=
    Over.μ_pullback_left_fst_snd P Q
  have ha : a ≫ cr = prod.snd ≫ byy := by
    dsimp only [a, cr]
    rw [Category.assoc, CartesianMonoidalCategory.tensorHom_snd, ← Category.assoc,
      OverProductTensorComparison.overProductTensorIso_hom_snd]
  have hal : a.left ≫ cr.left = (prod.snd : X ⨯ Y ⟶ Y).left ≫
      byy.left := congrArg Over.Hom.left ha
  have hc : byy.left ≫ pX = BY.coefficientEmbedding :=
    toHilbertConstruction_embedding_coefficient_fst BY
  change (a.left ≫ e.hom.left ≫ pA) ≫ c.left = _
  rw [Category.assoc, Category.assoc, he, ← Category.assoc, hal, Category.assoc, hc]
  rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.CoefficientMap.Core
