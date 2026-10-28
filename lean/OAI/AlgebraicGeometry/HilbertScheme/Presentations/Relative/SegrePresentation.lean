import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.ConstructionProjectivePresentationComparison
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.OverProductTensorComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.Open

/-! # Segre Presentation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.SegrePresentation.Core

noncomputable section

/-! An actual closed Segre embedding of the product of two projective
presentations over an arbitrary base scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

def relativeSegreOver (S : Scheme.{u}) (n m : ℕ) :
    AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S n ⊗ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S m ⟶
      AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S (AbelianModuli.HilbertConstruction.Affine.SegreOver.segreProjectiveDimension.{u} n m) :=
  (Functor.Monoidal.μIso (Over.pullback S.toSpecΓ)
    (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n)
    (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) m)).hom ≫
      (Over.pullback S.toSpecΓ).map (AbelianModuli.HilbertConstruction.Affine.SegreOver.affineSegreStandardEmbedding Γ(S, ⊤) n m)

theorem relativeSegreOver_isClosedImmersion (S : Scheme.{u}) (n m : ℕ) :
    IsClosedImmersion (relativeSegreOver S n m).left := by
  let e := Functor.Monoidal.μIso (Over.pullback S.toSpecΓ)
    (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n)
    (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) m)
  let : IsIso e.hom.left := ((Over.forget S).mapIso e).isIso_hom
  have hc := AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange.overPullback_map_closed
    (AbelianModuli.HilbertConstruction.Affine.SegreOver.affineSegreStandardEmbedding Γ(S, ⊤) n m) S.toSpecΓ
  change IsClosedImmersion (e.hom.left ≫
    ((Over.pullback S.toSpecΓ).map (AbelianModuli.HilbertConstruction.Affine.SegreOver.affineSegreStandardEmbedding Γ(S, ⊤) n m)).left)
  exact @IsClosedImmersion.comp _ _ _ _ _ inferInstance hc

def segreProductPresentation {S : Scheme.{u}} {X Y : Over S}
    (BX : Has.Core.ProjectivePresentation X) (BY : Has.Core.ProjectivePresentation Y) :
    Has.Core.ProjectivePresentation (X ⨯ Y) := by
  let e := OverProductTensorComparison.overProductTensorIso X Y
  let j := BX.toHilbertConstruction.embedding ⊗ₘ BY.toHilbertConstruction.embedding
  let k := relativeSegreOver S BX.dimension BY.dimension
  apply Has.Core.ProjectivePresentation.ofHilbertConstruction
  refine ⟨AbelianModuli.HilbertConstruction.Affine.SegreOver.segreProjectiveDimension.{u} BX.dimension BY.dimension, e.hom ≫ j ≫ k, ?_⟩
  let : IsIso e.hom.left := ((Over.forget S).mapIso e).isIso_hom
  have hj := AbelianModuli.HilbertConstruction.Projective.Products.overTensorMap_closed BX.toHilbertConstruction.embedding BY.toHilbertConstruction.embedding
  have hk := relativeSegreOver_isClosedImmersion S BX.dimension BY.dimension
  change IsClosedImmersion (e.hom.left ≫ j.left ≫ k.left)
  exact @IsClosedImmersion.comp _ _ _ _ _ inferInstance
    (@IsClosedImmersion.comp _ _ _ _ _ hj hk)

theorem segreProductPresentation_dimension {S : Scheme.{u}} {X Y : Over S}
    (BX : Has.Core.ProjectivePresentation X) (BY : Has.Core.ProjectivePresentation Y) :
    (segreProductPresentation BX BY).dimension =
      AbelianModuli.HilbertConstruction.Affine.SegreOver.segreProjectiveDimension.{u} BX.dimension BY.dimension := rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.SegrePresentation.Core
