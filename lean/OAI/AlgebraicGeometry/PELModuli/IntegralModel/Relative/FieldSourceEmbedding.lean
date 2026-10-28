import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.FieldEmbeddings
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Coefficient
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldBaseCoefficients

/-! # Field Source Embedding -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FieldSourceEmbedding

noncomputable section

/-! The actual source fiber embedding of an Presentations presentation is the
cartesian coefficient specialization of its source embedding. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace PolarizationEmbedding
universe u
variable {S : Scheme.{u}} {X : Over S}
    (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X)
    {K : Type u} [Field K] (a : Spec (.of K) ⟶ S)

def relativeFieldSourceEmbedding :
    pullback X.hom a ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K B.dimension) :=
  (Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldSourceIso (Z := X) a).inv ≫ Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding B a

theorem relativeFieldSourceEmbedding_closed :
    IsClosedImmersion (relativeFieldSourceEmbedding B a) := by
  have := Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding_closed B a
  dsimp only [relativeFieldSourceEmbedding]
  infer_instance

theorem relativeFieldSourceEmbedding_over :
    relativeFieldSourceEmbedding B a ≫ HilbertScheme.Presentations.Has.Core.projectiveSpaceMap K B.dimension =
      pullback.snd X.hom a := by
  rw [relativeFieldSourceEmbedding, Category.assoc, Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding_over,
    ← Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldSourceIso_snd (Z := X) a, Iso.inv_hom_id_assoc]

theorem relativeFieldSourceEmbedding_coefficient :
    relativeFieldSourceEmbedding B a ≫ AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affinePointCoefficients a) B.dimension =
      pullback.fst X.hom a ≫ B.coefficientEmbedding := by
  rw [relativeFieldSourceEmbedding, Category.assoc, Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding_coefficient,
    ← Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldSourceIso_fst (Z := X) a, ← Category.assoc, Iso.inv_hom_id_assoc]

theorem relativeFieldSourceEmbedding_isPullback [IsAffine S] :
    IsPullback (pullback.fst X.hom a) (relativeFieldSourceEmbedding B a)
      B.coefficientEmbedding (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affinePointCoefficients a) B.dimension) := by
  have hprojective : IsPullback (AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affinePointCoefficients a) B.dimension)
      (HilbertScheme.Presentations.Has.Core.projectiveSpaceMap K B.dimension)
      (HilbertScheme.Presentations.Has.Core.projectiveSpaceMap Γ(S, ⊤) B.dimension)
      (Spec.map (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affinePointCoefficients a)) :=
    AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap_isPullback (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affinePointCoefficients a) B.dimension
  have houter : IsPullback (pullback.fst X.hom a)
      (relativeFieldSourceEmbedding B a ≫ HilbertScheme.Presentations.Has.Core.projectiveSpaceMap K B.dimension)
      (B.coefficientEmbedding ≫ HilbertScheme.Presentations.Has.Core.projectiveSpaceMap Γ(S, ⊤) B.dimension)
      (Spec.map (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affinePointCoefficients a)) := by
    have hb : B.coefficientEmbedding ≫ HilbertScheme.Presentations.Has.Core.projectiveSpaceMap Γ(S, ⊤) B.dimension =
        X.hom ≫ S.toSpecΓ := Presentations.Coefficient.PolarizationEmbedding.e34CoefficientEmbedding_over B
    rw [relativeFieldSourceEmbedding_over, hb]
    exact FieldBaseCoefficients.PolarizationEmbedding.fieldBaseCoefficients_cartesian X a
  exact houter.of_bot (relativeFieldSourceEmbedding_coefficient B a).symm hprojective

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FieldSourceEmbedding
