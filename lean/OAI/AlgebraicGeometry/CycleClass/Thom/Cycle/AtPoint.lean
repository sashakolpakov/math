import OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift
import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.MeetingOpen

/-! # At Point -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.AtPoint.Constructions

noncomputable section

/-! Near a scheme point, components of a finite cycle which do not
contain that point can be removed without changing its relative class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) (x : V.carrier)
  (c : Geometric.DimensionCycles.RationalDimensionCycle V p)

def cycleAtPoint : Geometric.DimensionCycles.RationalDimensionCycle V p := c.filter (fun D => x ∈ (D.val : Set V.carrier))

def discardedOpen (D : Geometric.DimensionCycles.DimensionCycleSupport V p) : V.carrier.Opens :=
  if x ∈ (D.val : Set V.carrier) then ⊤ else ⟨(D.val : Set V.carrier)ᶜ, D.val.isClosed.isOpen_compl⟩

def pointNeighborhood (B : V.carrier.Opens) : V.carrier.Opens :=
  B ⊓ iInf (fun D : c.support => discardedOpen V p x D.val)

theorem pointNeighborhood_le (B : V.carrier.Opens) : pointNeighborhood V p x c B ≤ B := inf_le_left

theorem mem_pointNeighborhood (B : V.carrier.Opens) (hxB : x ∈ B) : x ∈ pointNeighborhood V p x c B := by
  classical
  refine ⟨hxB, ?_⟩
  change x ∈ ((iInf (fun D : c.support => discardedOpen V p x D.val) : V.carrier.Opens) : Set V.carrier)
  rw [Opens.coe_iInf]
  apply Set.mem_iInter.mpr
  intro D
  by_cases h : x ∈ (D.val.val : Set V.carrier)
  · rw [discardedOpen, ite_eq_left h]
    trivial
  · rw [discardedOpen, ite_eq_right h]
    exact h

theorem cycleAtPoint_ne_zero (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : cycleAtPoint V p x c D ≠ 0) :
    c D ≠ 0 ∧ x ∈ (D.val : Set V.carrier) := by
  classical
  change (if x ∈ (D.val : Set V.carrier) then c D else 0) ≠ 0 at hD
  split_ifs at hD with hx
  · exact ⟨hD, hx⟩
  · exact (hD rfl).elim

theorem coefficient_eq_on_neighborhood (B : V.carrier.Opens) (U : Opens V.analyticSpace)
    (hU : (U : Set V.analyticSpace) ⊆ Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver (pointNeighborhood V p x c B))
    (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : ∃ y : U, y.val ∈ Set.range D.analyticInclusion) :
    cycleAtPoint V p x c D = c D := by
  classical
  by_cases hxD : x ∈ (D.val : Set V.carrier)
  · exact Finsupp.filter_apply_pos _ _ hxD
  · have hc : c D = 0 := by
      by_contra hc
      obtain ⟨y, hyD⟩ := hD
      have hCD : pointNeighborhood V p x c B ≤ discardedOpen V p x D :=
        inf_le_right.trans (iInf_le (fun E : c.support => discardedOpen V p x E.val)
          ⟨D, Finsupp.mem_support_iff.mpr hc⟩)
      have hyC := hCD (hU y.property)
      change V.analyticUnderlying y.val ∈ discardedOpen V p x D at hyC
      rw [discardedOpen, ite_eq_right hxD] at hyC
      apply hyC
      rwa [D.range_analyticInclusion] at hyD
    exact (Finsupp.filter_apply_neg (fun E : Geometric.DimensionCycles.DimensionCycleSupport V p => x ∈ (E.val : Set V.carrier)) c hxD).trans hc.symm

theorem relativeClass_eq_cycleAtPoint (B : V.carrier.Opens) (U : Opens V.analyticSpace)
    (hU : (U : Set V.analyticSpace) ⊆ Scheme.SectionEvaluation.Constructions.analyticOpen V.toOver (pointNeighborhood V p x c B))
    (S : Set U)
    (hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 →
      (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ S) :
    Open.SupportedLift.Constructions.Map.relativeClassMap V U S p (Open.SupportedLift.Constructions.restrictCycle V U S p c) =
      Open.SupportedLift.Constructions.Map.relativeClassMap V U S p (Open.SupportedLift.Constructions.restrictCycle V U S p (cycleAtPoint V p x c)) := by
  apply Open.SupportedLift.Constructions.supportedClass_eq_of_local_coefficients V U S p c (cycleAtPoint V p x c) hc
  · intro D hD
    exact hc D (cycleAtPoint_ne_zero V p x c D hD).1
  · intro D hD
    exact (coefficient_eq_on_neighborhood V p x c B U hU D hD).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.AtPoint.Constructions
