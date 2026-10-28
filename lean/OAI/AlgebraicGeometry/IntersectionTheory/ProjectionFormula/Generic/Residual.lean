import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GenericSeparating
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResidualAvoidance

/-! # Residual -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.Residual

noncomputable section

/-! Residual avoidance and all prescribed pair-incidence bounds
are achieved by one actual finite projection. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Pair OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.Finite.Projection

abbrev map {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} {m : ℕ}
    (π : X.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)) : X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m := π.left

theorem avoids (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    (π : X.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m)) [IsFinite π.left]
    (W : IrreducibleCloseds X.carrier) (x : X.carrier) (hx : IsClosed {x})
    (he : ∃ U : X.carrier.Opens, x ∈ U ∧ Etale (U.ι ≫ map π))
    (hsep : ∀ y ∈ W, π.left y = π.left x → y = x) :
    x ∉ ResidualAvoidance.Projection.residual (map π) W := by
  obtain ⟨U, hxU, hU⟩ := he
  let := hU
  have hs : ∀ z : CycleClass.Geometric.GenericPoint.reducedSupportScheme W, map π (CycleClass.Geometric.GenericPoint.reducedSupportι W z) = map π x → CycleClass.Geometric.GenericPoint.reducedSupportι W z = x := by
    intro z hz
    apply hsep _ _ hz
    change CycleClass.Geometric.GenericPoint.reducedSupportι W z ∈ (W : Set X.carrier)
    rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι]
    exact Set.mem_range_self _
  have hav := ResidualGraph.Neighborhood.avoids_closure (map π) (CycleClass.Geometric.GenericPoint.reducedSupportι W)
    (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m) U x hx hxU hs
  have hr : Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ map π) = map π '' (W : Set X.carrier) := by
    change Set.range (map π ∘ CycleClass.Geometric.GenericPoint.reducedSupportι W) = _
    rw [Set.range_comp, CycleClass.Geometric.GenericPoint.range_reducedSupportι]
  change x ∉ closure (map π ⁻¹' (map π '' (W : Set X.carrier)) \ (W : Set X.carrier))
  simpa only [hr, CycleClass.Geometric.GenericPoint.range_reducedSupportι] using hav

theorem exists_projection (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    {τ ι : Type} [Finite τ] [Finite ι] (W Z : τ → IrreducibleCloseds X.carrier)
    (V : ι → IrreducibleCloseds X.carrier) (hV : ∀ j, 1 ≤ X.supportCodimension (V j))
    (x : ι → X.carrier) (hx : ∀ j, IsClosed {x j}) :
    ∃ π : X.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m), IsFinite π.left ∧
      (∀ j, x j ∉ ResidualAvoidance.Projection.residual (map π) (V j)) ∧
      ∀ t, ∀ C : IrreducibleCloseds (Support.Pair.space X (W t) (Z t)),
        (C : Set (Support.Pair.space X (W t) (Z t))) ⊆ Generic.Finite.Projection.coincidence X (W t) (Z t) π →
        ¬ (C : Set (Support.Pair.space X (W t) (Z t))) ⊆ Support.PairIncidenceStep.diagonal X (W t) (Z t) →
        Foundations.Scheme.SupportDimension.supportTranscendenceDimension C (Support.Pair.base X (W t) (Z t)) + m ≤
          Foundations.Scheme.SupportDimension.supportTranscendenceDimension (W t) X.structureMap + Foundations.Scheme.SupportDimension.supportTranscendenceDimension (Z t) X.structureMap := by
  obtain ⟨π, hfinite, hpoints, hI⟩ := GenericSeparating.Projection.exists_projection X m W Z V hV x hx
  let := hfinite
  exact ⟨π, hfinite, fun j => avoids X m π (V j) (x j) (hx j) (hpoints j).1 (hpoints j).2, hI⟩

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.Residual
