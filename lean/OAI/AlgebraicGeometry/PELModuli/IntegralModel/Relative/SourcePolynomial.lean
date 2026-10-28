import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatClosedProjectivePolynomials
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FieldSourceEmbedding

/-! # Source Polynomial -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.SourcePolynomial

noncomputable section

/-! A flat Presentations source presentation has an actual locally constant fiber
polynomial on its affine noetherian base. It computes every field source
embedding and is independent of the chosen field over the base point. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace PolarizationEmbedding
universe u
variable {S : Scheme.{u}} {X : Over S} (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X)

def e34SourceHilbertPolynomial (x : S) : Polynomial ℚ :=
  FlatHilbertPolynomialPartition.PolarizationEmbedding.residueHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf B.coefficientEmbedding.ker) (S.toSpecΓ x)

theorem e34SourceHilbertPolynomial_field_point
    {K : Type u} [Field K] (a : Spec (.of K) ⟶ S) :
    FlatHilbertPolynomialPartition.PolarizationEmbedding.residueHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf B.coefficientEmbedding.ker)
      ((IsLocalRing.closedPoint K).comap (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affinePointCoefficients a).hom) =
        e34SourceHilbertPolynomial B (a (IsLocalRing.closedPoint K)) := by
  change FlatHilbertPolynomialPartition.PolarizationEmbedding.residueHilbertPolynomial _ ((Spec.map (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affinePointCoefficients a)) (IsLocalRing.closedPoint K)) = _
  rw [AbelianModuli.HilbertConstruction.AffineProjective.Charts.affinePointCoefficients_spec]
  rfl

variable [IsAffine S] [Flat X.hom]

theorem e34CoefficientIdeal_flat :
    Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf B.coefficientEmbedding.ker))) := by
  have : IsClosedImmersion B.coefficientEmbedding := Presentations.Coefficient.PolarizationEmbedding.e34CoefficientEmbedding_closed B
  have hb : B.coefficientEmbedding ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(S, ⊤) B.dimension) =
      X.hom ≫ S.toSpecΓ := Presentations.Coefficient.PolarizationEmbedding.e34CoefficientEmbedding_over B
  have : Flat (B.coefficientEmbedding ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading Γ(S, ⊤) B.dimension)) := by
    rw [hb]
    infer_instance
  exact FlatClosedProjectivePolynomials.PolarizationEmbedding.closedProjective_homogeneousIdeal_flat B.coefficientEmbedding

variable [IsLocallyNoetherian S]

theorem e34SourceHilbertPolynomial_isLocallyConstant : IsLocallyConstant (e34SourceHilbertPolynomial B) := by
  let : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  let := e34CoefficientIdeal_flat B
  exact (FlatHilbertPolynomialPartition.PolarizationEmbedding.residueHilbertPolynomial_isLocallyConstant
    (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf B.coefficientEmbedding.ker)).comp_continuous S.toSpecΓ.continuous

theorem e34SourceHilbertPolynomial_finite_range : Set.Finite (Set.range (e34SourceHilbertPolynomial B)) :=
  (e34SourceHilbertPolynomial_isLocallyConstant B).range_finite

theorem relativeFieldSourceEmbedding_hasHilbertPolynomial
    {K : Type u} [Field K] (a : Spec (.of K) ⟶ S) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf (FieldSourceEmbedding.PolarizationEmbedding.relativeFieldSourceEmbedding B a).ker).toIdeal
      (e34SourceHilbertPolynomial B (a (IsLocalRing.closedPoint K))) := by
  let : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  have : IsClosedImmersion B.coefficientEmbedding := Presentations.Coefficient.PolarizationEmbedding.e34CoefficientEmbedding_closed B
  let := e34CoefficientIdeal_flat B
  rw [← e34SourceHilbertPolynomial_field_point B a]
  exact FlatClosedProjectivePolynomials.PolarizationEmbedding.closedProjectiveFiber_has_residueHilbertPolynomial B.coefficientEmbedding
    (AbelianModuli.HilbertConstruction.AffineProjective.Charts.affinePointCoefficients a).hom (FieldSourceEmbedding.PolarizationEmbedding.relativeFieldSourceEmbedding B a) (pullback.fst X.hom a)
    (FieldSourceEmbedding.PolarizationEmbedding.relativeFieldSourceEmbedding_isPullback B a)

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.SourcePolynomial
