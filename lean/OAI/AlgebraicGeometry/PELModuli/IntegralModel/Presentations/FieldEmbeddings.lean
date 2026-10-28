import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Hilbert
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.Charts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Field Embeddings -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.FieldEmbeddings

noncomputable section

/-! Actual field-valued coordinate embeddings for Presentations projective
presentations, constructed from their closed embeddings by base change. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace PolarizationEmbedding

universe u
variable {S : Scheme.{u}} {Z : Over S}
    (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation Z)
    {K : Type u} [Field K] (a : Spec (.of K) ⟶ S)

def e34FieldSourceIso :
    (Over.mk a ⨯ Z).left ≅ pullback Z.hom a :=
  Over.prodLeftIsoPullback (Over.mk a) Z ≪≫ pullbackSymmetry a Z.hom

theorem e34FieldSourceIso_fst :
    (e34FieldSourceIso (Z := Z) a).hom ≫ pullback.fst Z.hom a =
      (prod.snd : Over.mk a ⨯ Z ⟶ Z).left := by
  simp only [e34FieldSourceIso, Iso.trans_hom, Category.assoc,
    pullbackSymmetry_hom_comp_fst]
  exact Over.prodLeftIsoPullback_hom_snd (Over.mk a) Z

theorem e34FieldSourceIso_snd :
    (e34FieldSourceIso (Z := Z) a).hom ≫ pullback.snd Z.hom a =
      (prod.fst : Over.mk a ⨯ Z ⟶ Over.mk a).left := by
  simp only [e34FieldSourceIso, Iso.trans_hom, Category.assoc,
    pullbackSymmetry_hom_comp_snd]
  exact Over.prodLeftIsoPullback_hom_fst (Over.mk a) Z

def e34FieldEmbedding :
    (Over.mk a ⨯ Z).left ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K B.dimension) :=
  (e34FieldSourceIso (Z := Z) a).hom ≫
    ((Over.pullback a).map (Over.homMk B.embedding B.over_base : Z ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S B.dimension)).left ≫
    (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affineProjectiveChartMap_isPullback a B.dimension).isoPullback.inv

theorem e34FieldEmbedding_closed : IsClosedImmersion (e34FieldEmbedding B a) := by
  let i : Z ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S B.dimension := Over.homMk B.embedding B.over_base
  have hi : IsClosedImmersion i.left := B.closed
  let := hi
  have h := AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange.overPullback_map_closed i a
  let := h
  change IsClosedImmersion ((e34FieldSourceIso (Z := Z) a).hom ≫
    ((Over.pullback a).map i).left ≫
      (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affineProjectiveChartMap_isPullback a B.dimension).isoPullback.inv)
  infer_instance

theorem e34FieldEmbedding_projective :
    e34FieldEmbedding B a ≫ AbelianModuli.HilbertConstruction.AffineProjective.Charts.affineProjectiveChartMap a B.dimension =
      (prod.snd : Over.mk a ⨯ Z ⟶ Z).left ≫ B.embedding := by
  let H := AbelianModuli.HilbertConstruction.AffineProjective.Charts.affineProjectiveChartMap_isPullback a B.dimension
  have hq : H.isoPullback.inv ≫ AbelianModuli.HilbertConstruction.AffineProjective.Charts.affineProjectiveChartMap a B.dimension =
      pullback.fst (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S B.dimension).hom a :=
    (H.isoPullback.inv_comp_eq).mpr H.isoPullback_hom_fst.symm
  rw [e34FieldEmbedding, Category.assoc, Category.assoc, hq]
  rw [AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst, ← Category.assoc, e34FieldSourceIso_fst]
  rfl

theorem e34FieldEmbedding_over :
    e34FieldEmbedding B a ≫ HilbertScheme.Presentations.Has.Core.projectiveSpaceMap K B.dimension =
      (prod.fst : Over.mk a ⨯ Z ⟶ Over.mk a).left := by
  let H := AbelianModuli.HilbertConstruction.AffineProjective.Charts.affineProjectiveChartMap_isPullback a B.dimension
  have hq : H.isoPullback.inv ≫ HilbertScheme.Presentations.Has.Core.projectiveSpaceMap K B.dimension =
      pullback.snd (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S B.dimension).hom a :=
    (H.isoPullback.inv_comp_eq).mpr H.isoPullback_hom_snd.symm
  rw [e34FieldEmbedding, Category.assoc, Category.assoc, hq]
  rw [← Category.assoc]
  have hi : ((Over.pullback a).map
      (Over.homMk B.embedding B.over_base : Z ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S B.dimension)).left ≫
        pullback.snd (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S B.dimension).hom a = pullback.snd Z.hom a :=
    ((Over.pullback a).map
      (Over.homMk B.embedding B.over_base : Z ⟶ AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.projectiveSpaceOver S B.dimension)).w
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun h => (e34FieldSourceIso (Z := Z) a).hom ≫ h) hi).trans
      (e34FieldSourceIso_snd (Z := Z) a))

theorem e34FieldEmbedding_coefficient :
    e34FieldEmbedding B a ≫ AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affinePointCoefficients a) B.dimension =
      (prod.snd : Over.mk a ⨯ Z ⟶ Z).left ≫ B.coefficientEmbedding := by
  rw [← AbelianModuli.HilbertConstruction.AffineProjective.Charts.affineProjectiveChartMap_fst a B.dimension, ← Category.assoc,
    e34FieldEmbedding_projective, Category.assoc]
  rfl

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.FieldEmbeddings
