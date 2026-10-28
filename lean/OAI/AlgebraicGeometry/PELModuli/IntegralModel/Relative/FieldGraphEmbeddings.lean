import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.FieldEmbeddings
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.GraphPolarizationPowers

/-! # Field Graph Embeddings -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FieldGraphEmbeddings

noncomputable section

/-! The actual projective field embedding of a relative endomorphism
graph and its native twist sheaves. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace PolarizationEmbedding

variable {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
    (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation (A.scheme ⨯ A.scheme))
    {K : Type} [Field K] (a : Spec (.of K) ⟶ S)
    (v : (A.pullback a).scheme ⟶ (A.pullback a).scheme)

def relativeFieldGraphEmbedding :
    (A.pullback a).scheme.left ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K B.dimension) :=
  (EndomorphismHom.EndomorphismFamilies.homSourceSchemeIso A (Over.mk a)).inv ≫
    (HilbertScheme.Presentations.HomFunctor.Hom.graph A.scheme A.scheme (EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A (Over.mk a) v)).left ≫
      Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding B a

theorem relativeFieldGraphEmbedding_closed : IsClosedImmersion (relativeFieldGraphEmbedding A B a v) := by
  have hg := HilbertScheme.Presentations.HomFunctor.Hom.graph_isClosedImmersion A.scheme A.scheme (EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A (Over.mk a) v)
  let := hg
  have he := Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding_closed B a
  let := he
  dsimp only [relativeFieldGraphEmbedding]
  infer_instance

theorem relativeFieldGraphEmbedding_over :
    relativeFieldGraphEmbedding A B a v ≫ HilbertScheme.Presentations.Has.Core.projectiveSpaceMap K B.dimension =
      (A.pullback a).scheme.hom := by
  rw [relativeFieldGraphEmbedding, Category.assoc, Category.assoc, Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding_over,
    ← Over.comp_left, HilbertScheme.Presentations.HomFunctor.Hom.graph_fst]
  have h := EndomorphismHom.EndomorphismFamilies.homSourceSchemeIso_snd A (Over.mk a)
  exact ((EndomorphismHom.EndomorphismFamilies.homSourceSchemeIso A (Over.mk a)).inv_comp_eq).mpr h.symm

theorem relativeFieldGraphEmbedding_coefficient :
    relativeFieldGraphEmbedding A B a v ≫
      AbelianModuli.HilbertConstruction.Projective.CoefficientFunctoriality.polynomialProjectiveMap (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affinePointCoefficients a) B.dimension =
        GraphPolarizationPowers.PolarizationEmbedding.relativeGraphToProduct A (Over.mk a) v ≫ B.coefficientEmbedding := by
  rw [relativeFieldGraphEmbedding, Category.assoc, Category.assoc, Presentations.FieldEmbeddings.PolarizationEmbedding.e34FieldEmbedding_coefficient,
    ← Category.assoc (HilbertScheme.Presentations.HomFunctor.Hom.graph A.scheme A.scheme (EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A (Over.mk a) v)).left,
    ← Over.comp_left]
  have h : HilbertScheme.Presentations.HomFunctor.Hom.graph A.scheme A.scheme (EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A (Over.mk a) v) ≫ prod.snd =
      prod.lift (prod.snd : Over.mk a ⨯ A.scheme ⟶ A.scheme) (EndomorphismHom.EndomorphismFamilies.relativeHomEquiv A (Over.mk a) v) :=
    prod.lift_snd _ _
  rw [h, GraphPolarizationPowers.PolarizationEmbedding.relativeGraphToProduct, Category.assoc]

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FieldGraphEmbeddings
