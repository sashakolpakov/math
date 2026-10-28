import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SeparatingFinite
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResidualGraph

/-! # Residual Avoidance -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResidualAvoidance

noncomputable section

/-! Finite linear projections can make the residual closed set avoid
any prescribed finite family of closed points on positive-codimension supports. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Projection

def residual {X Y : Scheme} (π : X ⟶ Y) (W : IrreducibleCloseds X) : Closeds X :=
  ⟨closure (π ⁻¹' (π '' (W : Set X)) \ (W : Set X)), isClosed_closure⟩

theorem exists_projection (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    {ι : Type} [Finite ι] (W : ι → IrreducibleCloseds X.carrier)
    (hW : ∀ j, 1 ≤ X.supportCodimension (W j))
    (x : ι → X.carrier) (hx : ∀ j, IsClosed {x j}) :
    ∃ π : X.carrier ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace m,
      π ≫ Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m = X.structureMap ∧ IsFinite π ∧
      ∀ j, x j ∉ residual π (W j) := by
  let Z j : Closeds X.carrier := ⟨W j, (W j).isClosed⟩
  have hZ : ∀ j, ∀ C : IrreducibleCloseds X.carrier,
      (C : Set X.carrier) ⊆ Z j → 1 ≤ X.supportCodimension C := by
    intro j C hC
    exact (hW j).trans ((Supports.codimension_strictAnti X m).antitone hC)
  obtain ⟨π, hover, hfinite, hπ⟩ :=
    SeparatingFinite.Projection.exists_closed_points X m x hx Z hZ
  let := hfinite
  refine ⟨π, hover, hfinite, fun j => ?_⟩
  obtain ⟨⟨U, hxU, hU⟩, hsep⟩ := hπ j
  let := hU
  have hs : ∀ z : CycleClass.Geometric.GenericPoint.reducedSupportScheme (W j), π (CycleClass.Geometric.GenericPoint.reducedSupportι (W j) z) = π (x j) →
      CycleClass.Geometric.GenericPoint.reducedSupportι (W j) z = x j := by
    intro z hz
    apply hsep _ _ hz
    change CycleClass.Geometric.GenericPoint.reducedSupportι (W j) z ∈ (W j : Set X.carrier)
    rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι]
    exact Set.mem_range_self _
  have he := ResidualGraph.Neighborhood.avoids_closure π (CycleClass.Geometric.GenericPoint.reducedSupportι (W j))
    (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase m) U (x j) (hx j) hxU hs
  have hr : Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι (W j) ≫ π) = π '' (W j : Set X.carrier) := by
    change Set.range (π ∘ CycleClass.Geometric.GenericPoint.reducedSupportι (W j)) = _
    rw [Set.range_comp, CycleClass.Geometric.GenericPoint.range_reducedSupportι]
  change x j ∉ closure (π ⁻¹' (π '' (W j : Set X.carrier)) \ (W j : Set X.carrier))
  simpa only [hr, CycleClass.Geometric.GenericPoint.range_reducedSupportι] using he

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ResidualAvoidance
