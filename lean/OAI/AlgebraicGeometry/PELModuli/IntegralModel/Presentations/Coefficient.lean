import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Parameter
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Projective.HyperplanePowers

/-! # Coefficient -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Coefficient

noncomputable section

/-! The coefficient embedding of an Presentations projective presentation retains
the prescribed base map and is closed over an affine base. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

namespace PolarizationEmbedding

attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {S : Scheme.{u}} {X : Over S} (B : HilbertScheme.Presentations.Has.Core.ProjectivePresentation X)

theorem e34CoefficientEmbedding_over :
    B.coefficientEmbedding ≫ SheafCohomology.Projective.MvPolynomialClosure.MvPolynomial.homogeneousProjπ (R := Γ(S, ⊤)) = X.hom ≫ S.toSpecΓ := by
  change (B.embedding ≫ pullback.fst (HilbertScheme.Presentations.Has.Core.projectiveSpaceMap Γ(S, ⊤) B.dimension)
    S.toSpecΓ) ≫ HilbertScheme.Presentations.Has.Core.projectiveSpaceMap Γ(S, ⊤) B.dimension = _
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (fun f => f ≫ S.toSpecΓ) B.over_base

theorem e34CoefficientEmbedding_closed [IsAffine S] : IsClosedImmersion B.coefficientEmbedding := by
  have : IsClosedImmersion B.embedding := B.closed
  have : IsIso (pullback.fst (HilbertScheme.Presentations.Has.Core.projectiveSpaceMap Γ(S, ⊤) B.dimension) S.toSpecΓ) :=
    inferInstance
  dsimp only [HilbertScheme.Presentations.Has.Core.ProjectivePresentation.coefficientEmbedding]
  infer_instance

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.Coefficient
