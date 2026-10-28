import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.ProjectionCoincidence
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.EtaleNeighborhoods

/-! # Finite -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.Finite

noncomputable section

/-! Finite projections with simultaneous off-diagonal incidence
dimension bounds and etale neighborhoods at prescribed closed points. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Pair

attribute [local instance] PointJetCoordinates.scalar

def coincidence (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W Z : IrreducibleCloseds X.carrier)
    {Y : Over Foundations.Scheme.ProjectiveSpace.complexBase} (π : X.toOver ⟶ Y) [IsSeparated Y.hom] : Closeds (Support.Pair.space X W Z) :=
  Closed.Equalizer.locus (Support.Pair.first X W Z ≫ π) (Support.Pair.second X W Z ≫ π)

theorem exists_points (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    {τ ι : Type} [Finite τ] [Finite ι] (W Z : τ → IrreducibleCloseds X.carrier)
    (p : ι → (Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X.carrier)) (hp : ∀ j, p j ≫ X.structureMap = 𝟙 _) :
    ∃ π : X.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m), IsFinite π.left ∧
      (∀ j, ∃ U : X.carrier.Opens, p j (IsLocalRing.closedPoint ℂ) ∈ U ∧ Etale (U.ι ≫ π.left)) ∧
      ∀ t, ∀ C : IrreducibleCloseds (Support.Pair.space X (W t) (Z t)),
        (C : Set (Support.Pair.space X (W t) (Z t))) ⊆
          coincidence X (W t) (Z t) π →
        ¬ (C : Set (Support.Pair.space X (W t) (Z t))) ⊆ Support.PairIncidenceStep.diagonal X (W t) (Z t) →
        Foundations.Scheme.SupportDimension.supportTranscendenceDimension C (Support.Pair.base X (W t) (Z t)) + m ≤
          Foundations.Scheme.SupportDimension.supportTranscendenceDimension (W t) X.structureMap + Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Z t) X.structureMap := by
  let D j := (PointJetCoordinates.equivalence X (p j) (hp j) m).toLinearMap.comp
    (PointJetCoordinates.map X (p j) (hp j))
  have hD : ∀ j, Function.Surjective (D j) := fun j =>
    (PointJetCoordinates.equivalence X (p j) (hp j) m).surjective.comp
      (PointJetCoordinates.surjective X (p j) (hp j))
  obtain ⟨L, h, hI, hLI⟩ := Projection.Generic.Forms.exists_forms X m W Z D hD
  let π := Projection.ProjectionCoincidence.over X m L h
  refine ⟨π, inferInstanceAs (IsFinite (Projection.FiniteProjective.FromForms.map X m L h)), ?_, ?_⟩
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
        coincidence X (W t) (Z t) π :=
      Projection.ProjectionCoincidence.locus_eq X m L h (Support.Pair.first X (W t) (Z t)) (Support.Pair.second X (W t) (Z t))
    rw [he]
    exact hC

theorem exists_closed_points (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    {τ ι : Type} [Finite τ] [Finite ι] (W Z : τ → IrreducibleCloseds X.carrier)
    (x : ι → X.carrier) (hx : ∀ j, IsClosed {x j}) :
    ∃ π : X.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m), IsFinite π.left ∧
      (∀ j, ∃ U : X.carrier.Opens, x j ∈ U ∧ Etale (U.ι ≫ π.left)) ∧
      ∀ t, ∀ C : IrreducibleCloseds (Support.Pair.space X (W t) (Z t)),
        (C : Set (Support.Pair.space X (W t) (Z t))) ⊆
          coincidence X (W t) (Z t) π →
        ¬ (C : Set (Support.Pair.space X (W t) (Z t))) ⊆ Support.PairIncidenceStep.diagonal X (W t) (Z t) →
        Foundations.Scheme.SupportDimension.supportTranscendenceDimension C (Support.Pair.base X (W t) (Z t)) + m ≤
          Foundations.Scheme.SupportDimension.supportTranscendenceDimension (W t) X.structureMap + Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Z t) X.structureMap := by
  let p j := pointOfClosedPoint X.structureMap (x j) (hx j)
  have hp j : p j ≫ X.structureMap = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  obtain ⟨π, hfinite, hetale, hI⟩ := exists_points X m W Z p hp
  refine ⟨π, hfinite, ?_, hI⟩
  intro j
  have he : p j (IsLocalRing.closedPoint ℂ) = x j := pointOfClosedPoint_apply _ _ _ _
  simpa only [he] using hetale j

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.Finite
