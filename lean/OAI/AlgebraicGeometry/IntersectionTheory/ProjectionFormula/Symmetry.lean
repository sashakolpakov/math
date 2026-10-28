import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tor.Symmetry
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

/-! # Symmetry -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Symmetry

noncomputable section

/-! The exact native local intersection multiplicities are symmetric.
Their finite bilinear extension to divisor cycles is symmetric as well. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

theorem multiplicity_comm (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (A B C : IrreducibleCloseds X.carrier) :
    CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A B C = CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X B A C := by
  by_cases h : CycleClass.Thom.IntersectionGeometry.supportPoint C ∈ (A : Set X.carrier) ∩ (B : Set X.carrier)
  · rw [CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity, dite_eq_left h, CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity, dite_eq_left ⟨h.2, h.1⟩]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun n : ℕ∞ => (-1 : ℚ) ^ i * (n.toNat : ℚ))
      (Tor.Symmetry.length_comm (X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C))
        (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier A (CycleClass.Thom.IntersectionGeometry.supportPoint C) h.1)
        (CycleClass.Thom.IntersectionGeometry.localSupportModule X.carrier B (CycleClass.Thom.IntersectionGeometry.supportPoint C) h.2) i)
  · rw [CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity, dite_eq_right h, CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity,
      dite_eq_right (fun h' => h ⟨h'.2, h'.1⟩)]

theorem pair_proper_comm (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (A B : X.DimensionCycleSupport 1) :
    Supports.ProperCycle.pairMeetsProperly X 1 1 A B ↔ Supports.ProperCycle.pairMeetsProperly X 1 1 B A := by
  simp only [Supports.ProperCycle.pairMeetsProperly, Set.inter_comm]

theorem meetProperly_comm (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (a b : X.RationalDimensionCycle 1) :
    CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 1 a b ↔ CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 1 b a := by
  constructor <;> intro h A hA B hB C hC
  · exact h B hB A hA C (by simpa only [Set.inter_comm] using hC)
  · exact h B hB A hA C (by simpa only [Set.inter_comm] using hC)

theorem pairCycle_comm (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (A B : X.DimensionCycleSupport 1) :
    Supports.ProperCycle.pairCycle X m 1 1 A B = Supports.ProperCycle.pairCycle X m 1 1 B A := by
  by_cases h : Supports.ProperCycle.pairMeetsProperly X 1 1 A B
  · ext C
    rw [Supports.ProperCycle.pairCycle_apply X m 1 1 A B h,
      Supports.ProperCycle.pairCycle_apply X m 1 1 B A ((pair_proper_comm X A B).mp h), multiplicity_comm]
  · rw [Supports.ProperCycle.pairCycle, dite_eq_right h, Supports.ProperCycle.pairCycle,
      dite_eq_right (fun h' => h ((pair_proper_comm X A B).mpr h'))]

theorem bilinear_comm (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (a b : X.RationalDimensionCycle 1) :
    Supports.ProperCycle.intersectionBilinear X m 1 1 a b = Supports.ProperCycle.intersectionBilinear X m 1 1 b a := by
  simp only [Supports.ProperCycle.intersectionBilinear, Finsupp.linearCombination_apply, Finsupp.sum,
    LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B _
  apply Finset.sum_congr rfl
  intro A _
  rw [pairCycle_comm X m A B, mul_comm]

theorem proper_cycle_comm (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (a b : X.RationalDimensionCycle 1)
    (c : X.RationalDimensionCycle 2) (hc : CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X 1 1 a b c) :
    CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X 1 1 b a c := by
  have he := CycleClass.Thom.IntersectionGeometry.isProperIntersectionCycle_unique X 1 1 hc
    (Supports.ProperCycle.intersectionBilinear_isProper X m 1 1 a b hc.1)
  rw [he, bilinear_comm X m a b]
  exact Supports.ProperCycle.intersectionBilinear_isProper X m 1 1 b a ((meetProperly_comm X a b).mp hc.1)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Symmetry
