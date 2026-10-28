import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NamedReturnProjection
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpecIsoProjections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.ParameterProjections

/-! # Product Coefficient Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProductCoefficientMap

noncomputable section

/-! The existing projective product presentation projects to the actual
affine Segre morphism over the global coefficient ring. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false

private abbrev coefficient_return_equation (S : Scheme.{u}) (d : ℕ) :=
  ((PresentationBaseChange.nativeAffineProjectivePresentation Γ(S, ⊤) d).baseChangeIso_hom S.toSpecΓ).symm.trans
    (SpecIsoProjections.projectiveCoefficientReturnIso_hom S d)

variable (S : Scheme.{u}) (n m : ℕ)

def relativeProjectiveProductCoefficientMap :
    (ProjectivePresentations.projectiveSpaceOver S n ⊗ ProjectivePresentations.projectiveSpaceOver S m).left ⟶
      (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n ⊗ ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) m).left :=
  Graph.FamilyNaturality.overProductBaseChangeMap S.toSpecΓ (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n) (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) m)

theorem relativeProjectiveProductCoefficientMap_fst :
    relativeProjectiveProductCoefficientMap S n m ≫
      (fst (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n) (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) m)).left =
    (fst (ProjectivePresentations.projectiveSpaceOver S n) (ProjectivePresentations.projectiveSpaceOver S m)).left ≫
      RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection S n :=
  Product.ParameterProjections.overProductBaseChangeMap_fst S.toSpecΓ _ _

theorem relativeProjectiveProductCoefficientMap_snd :
    relativeProjectiveProductCoefficientMap S n m ≫
      (snd (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n) (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) m)).left =
    (snd (ProjectivePresentations.projectiveSpaceOver S n) (ProjectivePresentations.projectiveSpaceOver S m)).left ≫
      RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection S m :=
  Product.ParameterProjections.overProductBaseChangeMap_snd S.toSpecΓ _ _

private theorem product_embedding_shape :
    (Products.projectiveSpaceProductPresentation S n m).embedding =
      Pullback.ReturnEmbedding.pullbackReturnEmbedding S.toSpecΓ (Affine.SegreOver.affineSegreStandardEmbedding Γ(S, ⊤) n m)
        (SpaceBaseChange.projectiveSpaceOverSpecIso Γ(S, ⊤) (Affine.SegreOver.segreProjectiveDimension.{u} n m)).inv
        (SpaceBaseChange.projectiveSpaceOverBaseChangeIso S.toSpecΓ (Affine.SegreOver.segreProjectiveDimension.{u} n m)).inv
        (Functor.Monoidal.μIso (Over.pullback S.toSpecΓ)
          (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n) (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) m)).hom := rfl

private theorem coefficient_projection_shape (d : ℕ) :
    RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection S d =
      pullback.fst (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) d).hom S.toSpecΓ := rfl

private theorem product_coefficient_map_shape :
    relativeProjectiveProductCoefficientMap S n m =
      (Functor.Monoidal.μIso (Over.pullback S.toSpecΓ)
        (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n) (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) m)).hom.left ≫
      pullback.fst (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n ⊗ ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) m).hom
        S.toSpecΓ := rfl

private abbrev native_product_projection :=
  NamedReturnProjection.pullbackReturnEmbedding_projection_named S.toSpecΓ
    (Affine.SegreOver.affineSegreStandardEmbedding Γ(S, ⊤) n m)
    (SpaceBaseChange.projectiveSpaceOverSpecIso Γ(S, ⊤) (Affine.SegreOver.segreProjectiveDimension.{u} n m)).inv
    (SpaceBaseChange.projectiveSpaceOverBaseChangeIso S.toSpecΓ (Affine.SegreOver.segreProjectiveDimension.{u} n m))
    (Functor.Monoidal.μIso (Over.pullback S.toSpecΓ)
      (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) n) (ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) m)).hom
    (coefficient_return_equation S (Affine.SegreOver.segreProjectiveDimension.{u} n m))

theorem projectiveSpaceProductPresentation_coefficients :
    (Products.projectiveSpaceProductPresentation S n m).embedding.left ≫
      RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection S (Affine.SegreOver.segreProjectiveDimension.{u} n m) =
    relativeProjectiveProductCoefficientMap S n m ≫
      (Affine.SegreOver.affineSegreStandardEmbedding Γ(S, ⊤) n m).left := by
  rw [product_embedding_shape, coefficient_projection_shape, product_coefficient_map_shape]
  exact native_product_projection S n m

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProductCoefficientMap
