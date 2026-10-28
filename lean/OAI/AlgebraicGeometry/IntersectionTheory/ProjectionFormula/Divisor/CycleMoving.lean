import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveCycleMoving
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.RightZero
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

/-! # Cycle Moving -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.CycleMoving

noncomputable section

/-! Divisors and cycles of arbitrary codimension admit actual properly
meeting representatives in every dimension, including disconnected schemes. -/

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

theorem of_avoiding (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a : X.RationalDimensionCycle 1) (b : X.RationalDimensionCycle q)
    (h : ∀ D ∈ a.support, ∀ A ∈ b.support, ¬ A.val ≤ D.val) : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 q a b := by
  intro D hD A hA C hC
  have hCA : C ≤ A.val := fun _ hx => (hC hx).2
  have hn : C ≠ A.val := by
    intro he
    exact h D hD A hA (fun x hx => (hC (he ▸ hx)).1)
  have hh := Supports.codimension_strictAnti X m (lt_of_le_of_ne hCA hn)
  rw [A.property] at hh
  omega

theorem move_pair (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a c : X.RationalDimensionCycle 1) (b : X.RationalDimensionCycle q) :
    ∃ b' : X.RationalDimensionCycle q, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X q b b' ∧
      CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 q a b' ∧ CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 q c b' := by
  cases q with
  | zero =>
    exact ⟨b, CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X 0 b,
      (RightZero.cycleIntersection_isProper X m 1 a b).1,
      (RightZero.cycleIntersection_isProper X m 1 c b).1⟩
  | succ r =>
    obtain ⟨b', hb', hav⟩ := PositiveCycleMoving.move X m r 1 (by decide) (a.support ∪ c.support) b
    exact ⟨b', hb', of_avoiding X m (r + 1) a b'
      (fun D hD A hA => hav A hA D (Finset.mem_union_left _ hD)),
      of_avoiding X m (r + 1) c b'
      (fun D hD A hA => hav A hA D (Finset.mem_union_right _ hD))⟩

theorem properly_meeting_representatives (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a : X.RationalDimensionCycle 1) (b : X.RationalDimensionCycle q) :
    ∃ b' : X.RationalDimensionCycle q, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X q b b' ∧ CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 q a b' := by
  obtain ⟨b', hb', ha, _⟩ := move_pair X m q a a b
  exact ⟨b', hb', ha⟩

theorem representsIntersection_exists (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a : X.RationalDimensionCycle 1) (b : X.RationalDimensionCycle q) :
    ∃ c : X.RationalDimensionCycle (1 + q), CycleClass.Thom.IntersectionGeometry.RepresentsIntersection X 1 q a b c := by
  obtain ⟨b', hb', hp⟩ := properly_meeting_representatives X m q a b
  obtain ⟨c, hc, _⟩ := Supports.ProperCycle.properIntersection_exists_unique X m 1 q a b' hp
  exact ⟨c, a, b', c, CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X 1 a, hb', hc,
    CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X (1 + q) c⟩

theorem chowIntersection_nonempty (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (a : ProperCycleLinearity.ChowQ X 1) (b : ProperCycleLinearity.ChowQ X q) :
    (ProperCycleLinearity.chowIntersection X 1 q a b).Nonempty := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X 1 a
  obtain ⟨b, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X q b
  obtain ⟨c, hc⟩ := representsIntersection_exists X m q a b
  exact ⟨ProperCycleLinearity.cycleToChowQ X (1 + q) c, (ProperCycleLinearity.chowIntersection_mk_iff X 1 q a b c).mpr hc⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.CycleMoving
