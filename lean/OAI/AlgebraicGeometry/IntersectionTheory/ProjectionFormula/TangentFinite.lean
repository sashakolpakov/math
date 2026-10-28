import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PointJetCoordinates
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.FiniteProjective

/-! # Tangent Finite -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TangentFinite

noncomputable section

/-! A finite projective projection can be chosen so that its defining
linear forms give a basis of first-order data at each of finitely many points. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Projection

attribute [local instance] PointJetCoordinates.scalar

theorem exists_projection (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    {ι : Type} [Finite ι] (p : ι → (Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X.carrier))
    (hp : ∀ j, p j ≫ X.structureMap = 𝟙 _) :
    ∃ (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
      (h : ∀ x : X.carrier, ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal),
      Projection.FiniteProjective.FromForms.map X m L h ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m = X.structureMap ∧
      IsFinite (Projection.FiniteProjective.FromForms.map X m L h) ∧
      ∀ j, LinearIndependent ℂ (fun a => PointJetCoordinates.map X (p j) (hp j) (L a)) ∧
        Submodule.span ℂ (Set.range (fun a => PointJetCoordinates.map X (p j) (hp j) (L a))) = ⊤ := by
  obtain ⟨L, h, hLI⟩ := PointJetCoordinates.exists_forms X m p hp
  refine ⟨L, h, Projection.FiniteProjective.FromForms.over_base X m L h, inferInstance, fun j => ⟨hLI j, ?_⟩⟩
  let := PointJetCoordinates.finite X (p j) (hp j) m
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_span_eq_card (hLI j), Fintype.card_fin, PointJetCoordinates.dimension X (p j) (hp j) m]

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.TangentFinite
