import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SurfaceCurvePrime

/-! # Nested Support Points -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupportPoints

noncomputable section

/-! Membership in the inner support is exactly membership in the
ambient support, and its local prime is the actual nested-stalk kernel. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupport

variable (X : Scheme) (A W : IrreducibleCloseds X) (hAW : A ≤ W)

theorem inner_coe : (NestedSupport.innerSupport X A W hAW : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) =
    Set.range (NestedSupport.inclusion X A W hAW) := by
  change closure (Set.range (NestedSupport.inclusion X A W hAW)) = _
  exact (NestedSupport.inclusion X A W hAW).isClosedEmbedding.isClosed_range.closure_eq

theorem mem_iff (y : CycleClass.Geometric.GenericPoint.reducedSupportScheme W) : y ∈ (NestedSupport.innerSupport X A W hAW : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) ↔
    CycleClass.Geometric.GenericPoint.reducedSupportι W y ∈ (A : Set X) := by
  rw [inner_coe]
  constructor
  · rintro ⟨z, rfl⟩
    have he := congrArg (fun f : CycleClass.Geometric.GenericPoint.reducedSupportScheme A ⟶ X => f z) (NestedSupport.inclusion_fac X A W hAW)
    change CycleClass.Geometric.GenericPoint.reducedSupportι W (NestedSupport.inclusion X A W hAW z) = CycleClass.Geometric.GenericPoint.reducedSupportι A z at he
    rw [he, ← CycleClass.Geometric.GenericPoint.range_reducedSupportι]
    exact ⟨z, rfl⟩
  · intro hy
    let z := CycleClass.Thom.IntersectionGeometry.supportPreimage A (CycleClass.Geometric.GenericPoint.reducedSupportι W y) hy
    refine ⟨z, ?_⟩
    apply (CycleClass.Geometric.GenericPoint.reducedSupportι W).isEmbedding.injective
    have he := congrArg (fun f : CycleClass.Geometric.GenericPoint.reducedSupportScheme A ⟶ X => f z) (NestedSupport.inclusion_fac X A W hAW)
    exact he.trans (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec A _ hy)

theorem preimage_mem_iff (x : X) (hxW : x ∈ (W : Set X)) :
    CycleClass.Thom.IntersectionGeometry.supportPreimage W x hxW ∈ (NestedSupport.innerSupport X A W hAW : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) ↔ x ∈ (A : Set X) := by
  rw [mem_iff, CycleClass.Thom.IntersectionGeometry.supportPreimage_spec]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupportPoints
