import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.Finite
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.CoordinateNormalForm

/-! # Coordinate Data -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.CoordinateData

noncomputable section

/-! Retain the actual homogeneous coordinates of the generic
projection, together with independence, etale points and incidence bounds. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Pair OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.Finite.Projection

attribute [local instance] PointJetCoordinates.scalar

theorem exists_points (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    {τ ι : Type} [Finite τ] [Finite ι] [Nonempty ι] (W Z : τ → IrreducibleCloseds X.carrier)
    (p : ι → (Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X.carrier)) (hp : ∀ j, p j ≫ X.structureMap = 𝟙 _) :
    ∃ (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
      (h : ∀ x : X.carrier, ∃ a, (L a).val ∉ (X.embedding x).asHomogeneousIdeal),
      LinearIndependent ℂ L ∧
      (∀ j, ∃ U : X.carrier.Opens, p j (IsLocalRing.closedPoint ℂ) ∈ U ∧
        Etale (U.ι ≫ Projection.FiniteProjective.FromForms.map X m L h)) ∧
      ∀ t, ∀ C : IrreducibleCloseds (Support.Pair.space X (W t) (Z t)),
        (C : Set (Support.Pair.space X (W t) (Z t))) ⊆
          Generic.Finite.Projection.coincidence X (W t) (Z t) (Projection.ProjectionCoincidence.over X m L h) →
        ¬ (C : Set (Support.Pair.space X (W t) (Z t))) ⊆ Support.PairIncidenceStep.diagonal X (W t) (Z t) →
        Foundations.Scheme.SupportDimension.supportTranscendenceDimension C (Support.Pair.base X (W t) (Z t)) + m ≤
          Foundations.Scheme.SupportDimension.supportTranscendenceDimension (W t) X.structureMap + Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Z t) X.structureMap := by
  let D j := (PointJetCoordinates.equivalence X (p j) (hp j) m).toLinearMap.comp
    (PointJetCoordinates.map X (p j) (hp j))
  have hD : ∀ j, Function.Surjective (D j) := fun j =>
    (PointJetCoordinates.equivalence X (p j) (hp j) m).surjective.comp
      (PointJetCoordinates.surjective X (p j) (hp j))
  obtain ⟨L, h, hI, hLI⟩ := Projection.Generic.Forms.exists_forms X m W Z D hD
  let j₀ : ι := Classical.choice inferInstance
  refine ⟨L, h, LinearIndependent.of_comp (D j₀) (hLI j₀), ?_, ?_⟩
  · intro j
    have hi : LinearIndependent ℂ (fun a => PointJetCoordinates.map X (p j) (hp j) (L a)) :=
      LinearIndependent.of_comp (PointJetCoordinates.equivalence X (p j) (hp j) m).toLinearMap (hLI j)
    have hspan : Submodule.span ℂ
        (Set.range (fun a => PointJetCoordinates.map X (p j) (hp j) (L a))) = ⊤ := by
      let := PointJetCoordinates.finite X (p j) (hp j) m
      apply Submodule.eq_top_of_finrank_eq
      rw [finrank_span_eq_card hi, Fintype.card_fin, PointJetCoordinates.dimension X (p j) (hp j) m]
    have hu := Projection.StalkUnramified.unramified X m L h (p j) (hp j) hspan
    let := Projective.Dimension.projective_relativeDimension m
    have he := Smooth.EqualDimensionEtale.stalk (Projection.FiniteProjective.FromForms.map X m L h)
      X.structureMap (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m) (Projection.FiniteProjective.FromForms.over_base X m L h)
      m (p j (IsLocalRing.closedPoint ℂ)) hu
    exact ProjectionFormula.Etale.StalkNeighborhood.exists_open (Projection.FiniteProjective.FromForms.map X m L h)
      (p j (IsLocalRing.closedPoint ℂ)) he
  · intro t C hC hdiag
    apply hI t C _ hdiag
    have he : Support.PairIncidenceStep.incidence X (W t) (Z t) m L =
        Generic.Finite.Projection.coincidence X (W t) (Z t) (Projection.ProjectionCoincidence.over X m L h) :=
      Projection.ProjectionCoincidence.locus_eq X m L h (Support.Pair.first X (W t) (Z t)) (Support.Pair.second X (W t) (Z t))
    rw [he]
    exact hC

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.CoordinateData
