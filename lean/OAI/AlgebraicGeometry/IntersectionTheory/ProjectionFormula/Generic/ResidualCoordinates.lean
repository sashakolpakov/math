import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.CoordinateData
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.Residual

/-! # Residual Coordinates -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.ResidualCoordinates

noncomputable section

/-! The residual construction retains independent linear
coordinates and etale neighborhoods for the subsequent ambient cone. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Pair OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.Finite.Projection

theorem exists_coordinates (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    {τ ι : Type} [Finite τ] [Finite ι] [Nonempty ι] (W Z : τ → IrreducibleCloseds X.carrier)
    (V : ι → IrreducibleCloseds X.carrier) (hV : ∀ j, 1 ≤ X.supportCodimension (V j))
    (x : ι → X.carrier) (hx : ∀ j, IsClosed {x j}) :
    ∃ (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading X.ambientDimension 1)
      (h : ∀ y : X.carrier, ∃ a, (L a).val ∉ (X.embedding y).asHomogeneousIdeal),
      LinearIndependent ℂ L ∧
      (∀ j, (∃ U : X.carrier.Opens, x j ∈ U ∧ Etale (U.ι ≫ Projection.FiniteProjective.FromForms.map X m L h)) ∧
        x j ∉ ResidualAvoidance.Projection.residual (Projection.FiniteProjective.FromForms.map X m L h) (V j)) ∧
      ∀ t, ∀ C : IrreducibleCloseds (Support.Pair.space X (W t) (Z t)),
        (C : Set (Support.Pair.space X (W t) (Z t))) ⊆
          Generic.Finite.Projection.coincidence X (W t) (Z t) (Projection.ProjectionCoincidence.over X m L h) →
        ¬ (C : Set (Support.Pair.space X (W t) (Z t))) ⊆ Support.PairIncidenceStep.diagonal X (W t) (Z t) →
        Foundations.Scheme.SupportDimension.supportTranscendenceDimension C (Support.Pair.base X (W t) (Z t)) + m ≤
          Foundations.Scheme.SupportDimension.supportTranscendenceDimension (W t) X.structureMap + Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Z t) X.structureMap := by
  let A : τ ⊕ ι → IrreducibleCloseds X.carrier := Sum.elim W V
  let B : τ ⊕ ι → IrreducibleCloseds X.carrier :=
    Sum.elim Z (fun j => irreducibleSetEquivPoints.symm (x j))
  let p j := pointOfClosedPoint X.structureMap (x j) (hx j)
  have hp j : p j ≫ X.structureMap = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  obtain ⟨L, h, hLI, hetale, hI⟩ := CoordinateData.Projection.exists_points X m A B p hp
  let π := Projection.ProjectionCoincidence.over X m L h
  let : IsFinite π.left := inferInstanceAs (IsFinite (Projection.FiniteProjective.FromForms.map X m L h))
  refine ⟨L, h, hLI, ?_, fun t => hI (Sum.inl t)⟩
  intro j
  have he : ∃ U : X.carrier.Opens, x j ∈ U ∧ Etale (U.ι ≫ Projection.FiniteProjective.FromForms.map X m L h) := by
    have hpj : p j (IsLocalRing.closedPoint ℂ) = x j := pointOfClosedPoint_apply _ _ _ _
    simpa only [hpj] using hetale j
  refine ⟨he, ?_⟩
  have hd : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (V j) X.structureMap +
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (x j)) X.structureMap < m := by
    rw [Closed.PointDimension.support_dimension X.structureMap (x j) (hx j)]
    have he := Grading.supportDimension_add_codimension X m (V j)
    have hv := hV j
    omega
  have hs := GenericSeparating.IncidenceFiberSeparation.subset_of_dimension (Support.Pair.base X (V j) (irreducibleSetEquivPoints.symm (x j)))
    (Generic.Finite.Projection.coincidence X (V j) (irreducibleSetEquivPoints.symm (x j)) π)
    (Support.PairIncidenceStep.diagonal X (V j) (irreducibleSetEquivPoints.symm (x j)))
    m _ hd (hI (Sum.inr j))
  exact Residual.Projection.avoids X m π (V j) (x j) (hx j) he
    (GenericSeparating.IncidenceFiberSeparation.fiber_eq X m π (V j) (x j) (hx j) hs)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.ResidualCoordinates
