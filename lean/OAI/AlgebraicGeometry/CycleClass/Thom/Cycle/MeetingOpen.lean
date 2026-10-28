import OAI.AlgebraicGeometry.CycleClass.Thom.IntersectionGeometry
import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.SupportRegularBoundary

/-! # Meeting Open -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.MeetingOpen.Constructions

noncomputable section

/-! If an original integral cycle meets an analytic open inside an
algebraic open, its actual generic support point lies in that algebraic open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem supportPoint_mem_of_meets {X : Scheme} (C : IrreducibleCloseds X) (B : X.Opens)
    (x : X) (hxC : x ∈ (C : Set X)) (hxB : x ∈ B) : IntersectionGeometry.supportPoint C ∈ B :=
  ((C.isIrreducible.isGenericPoint_genericPoint C.isClosed).mem_open_set_iff B.isOpen).mpr ⟨x, hxC, hxB⟩

theorem supportPoint_mem_of_analytic_meets (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) {p : ℕ}
    (C : Geometric.DimensionCycles.DimensionCycleSupport V p) (B : V.carrier.Opens) (U : Opens V.analyticSpace)
    (hU : (U : Set V.analyticSpace) ⊆ Thom.Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver B)
    (hC : ∃ x : U, x.val ∈ Set.range C.analyticInclusion) : IntersectionGeometry.supportPoint C.val ∈ B := by
  obtain ⟨x, hx⟩ := hC
  have hxC : V.analyticUnderlying x.val ∈ (C.val : Set V.carrier) := by
    rwa [C.range_analyticInclusion] at hx
  exact supportPoint_mem_of_meets C.val B (V.analyticUnderlying x.val) hxC (hU x.property)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.MeetingOpen.Constructions
