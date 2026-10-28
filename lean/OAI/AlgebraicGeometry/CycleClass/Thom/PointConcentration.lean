import OAI.AlgebraicGeometry.CycleClass.Thom.Local.EulerEmpty

/-! # Point Concentration -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PointConcentration.Constructions

noncomputable section

/-! Near a target's generic point, a cycle in the target grading is
exactly its original coefficient times that target support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.AtPoint.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Local.EulerEmpty.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (C : Geometric.DimensionCycles.DimensionCycleSupport V p)
  (c : Geometric.DimensionCycles.RationalDimensionCycle V p)

theorem cycleAtPoint_eq_single : Cycle.AtPoint.Constructions.cycleAtPoint V p (IntersectionGeometry.supportPoint C.val) c = Finsupp.single C (c C) := by
  ext D
  by_cases h : D = C
  · subst D
    have hx : IntersectionGeometry.supportPoint C.val ∈ (C.val : Set V.carrier) :=
      C.val.isIrreducible.isGenericPoint_genericPoint C.val.isClosed |>.mem
    exact (Finsupp.filter_apply_pos (fun D : Geometric.DimensionCycles.DimensionCycleSupport V p => IntersectionGeometry.supportPoint C.val ∈ (D.val : Set V.carrier)) c hx).trans
      (Finsupp.single_eq_same).symm
  · have hx : IntersectionGeometry.supportPoint C.val ∉ (D.val : Set V.carrier) := fun hx => h (Local.EulerEmpty.Constructions.support_eq_of_generic_mem V p C D hx)
    exact (Finsupp.filter_apply_neg (fun D : Geometric.DimensionCycles.DimensionCycleSupport V p => IntersectionGeometry.supportPoint C.val ∈ (D.val : Set V.carrier)) c hx).trans
      (by simp only [Finsupp.single_apply, ite_eq_right (Ne.symm h)])

theorem relativeClass_eq_single_near_generic (B : V.carrier.Opens) (U : Opens V.analyticSpace)
    (hU : (U : Set V.analyticSpace) ⊆ Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver (Cycle.AtPoint.Constructions.pointNeighborhood V p (IntersectionGeometry.supportPoint C.val) c B))
    (S : Set U)
    (hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 →
      (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ S) :
    Open.SupportedLift.Constructions.Map.relativeClassMap V U S p (Open.SupportedLift.Constructions.restrictCycle V U S p c) =
      Open.SupportedLift.Constructions.Map.relativeClassMap V U S p (Open.SupportedLift.Constructions.restrictCycle V U S p (Finsupp.single C (c C))) := by
  have h := Cycle.AtPoint.Constructions.relativeClass_eq_cycleAtPoint V p (IntersectionGeometry.supportPoint C.val) c B U hU S hc
  rwa [cycleAtPoint_eq_single] at h

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PointConcentration.Constructions
