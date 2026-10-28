import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.PrincipalCycleDescent
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.SimultaneousMoving
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

/-! # Divisor Descent -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.DivisorDescent

noncomputable section

/-! Divisor intersection on an integral smooth projective scheme respects
the full native rational-equivalence submodule in every positive codimension. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m k : ℕ)
  [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]

theorem transfer_zero (a a' : X.RationalDimensionCycle 1) (b : X.RationalDimensionCycle (k + 1))
    (ha : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 a a') (hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 (k + 1) a b)
    (hp' : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 (k + 1) a' b)
    (hz : Supports.ProperCycle.intersectionBilinear X m 1 (k + 1) a' b ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (1 + (k + 1))) :
    Supports.ProperCycle.intersectionBilinear X m 1 (k + 1) a b ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (1 + (k + 1)) := by
  have he := DivisorLeftDescent.intersection_congr_left X m (k + 1) a a' b ha hp hp'
  simpa only [sub_add_cancel] using (Submodule.add_mem (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (1 + (k + 1))) he hz :
    Supports.ProperCycle.intersectionBilinear X m 1 (k + 1) a b - Supports.ProperCycle.intersectionBilinear X m 1 (k + 1) a' b +
      Supports.ProperCycle.intersectionBilinear X m 1 (k + 1) a' b ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (1 + (k + 1)))

theorem relation (b : X.RationalDimensionCycle (k + 1)) (hb : b ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (k + 1))
    (a : X.RationalDimensionCycle 1) (hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 (k + 1) a b) :
    Supports.ProperCycle.intersectionBilinear X m 1 (k + 1) a b ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X (1 + (k + 1)) := by
  revert a
  induction hb using Submodule.span_induction with
  | mem b hb => exact fun a hp => PrincipalCycleDescent.generator X m k b hb a hp
  | zero =>
    intro a _
    rw [map_zero]
    exact Submodule.zero_mem _
  | add b c _ _ ihb ihc =>
    intro a hp
    obtain ⟨a', ha', hpb, hpc⟩ := Divisor.SimultaneousMoving.move_pair X m (k + 1) a b c
    apply transfer_zero X m k a a' (b + c) ha' hp (ProperCycleLinearity.add_right X 1 (k + 1) a' b c hpb hpc)
    rw [map_add]
    exact Submodule.add_mem _ (ihb a' hpb) (ihc a' hpc)
  | smul q b _ ih =>
    intro a hp
    obtain ⟨a', ha', hp', _⟩ := Divisor.SimultaneousMoving.move_pair X m (k + 1) a b b
    apply transfer_zero X m k a a' (q • b) ha' hp (ProperCycleLinearity.smul_right X 1 (k + 1) a' b q hp')
    rw [map_smul]
    exact Submodule.smul_mem _ _ (ih a' hp')

theorem intersection_congr_right (a : X.RationalDimensionCycle 1) (b b' : X.RationalDimensionCycle (k + 1))
    (hb : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (k + 1) b b') (hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 (k + 1) a b)
    (hp' : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 (k + 1) a b') :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (1 + (k + 1)) (Supports.ProperCycle.intersectionBilinear X m 1 (k + 1) a b) (Supports.ProperCycle.intersectionBilinear X m 1 (k + 1) a b') := by
  have h := relation X m k (b - b') hb a (ProperCycleLinearity.sub_right X 1 (k + 1) a b b' hp hp')
  rw [map_sub] at h
  exact h

theorem intersection_congr (a a' : X.RationalDimensionCycle 1) (b b' : X.RationalDimensionCycle (k + 1))
    (ha : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 a a') (hb : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (k + 1) b b')
    (hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 (k + 1) a b) (hp' : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 (k + 1) a' b') :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (1 + (k + 1)) (Supports.ProperCycle.intersectionBilinear X m 1 (k + 1) a b) (Supports.ProperCycle.intersectionBilinear X m 1 (k + 1) a' b') := by
  obtain ⟨u, hau, hub, hub'⟩ := Divisor.SimultaneousMoving.move_pair X m (k + 1) a b b'
  have hua' := CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X 1 (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_symm X 1 hau) ha
  exact CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X (1 + (k + 1))
    (DivisorLeftDescent.intersection_congr_left X m (k + 1) a u b hau hp hub)
    (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X (1 + (k + 1)) (intersection_congr_right X m k u b b' hb hub hub')
      (DivisorLeftDescent.intersection_congr_left X m (k + 1) u a' b' hua' hub' hp'))

include m in
theorem proper_intersections_congr (a a' : X.RationalDimensionCycle 1) (b b' : X.RationalDimensionCycle (k + 1))
    (ha : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 a a') (hb : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (k + 1) b b')
    (c c' : X.RationalDimensionCycle (1 + (k + 1)))
    (hc : CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X 1 (k + 1) a b c)
    (hc' : CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X 1 (k + 1) a' b' c') : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X (1 + (k + 1)) c c' := by
  have he := CycleClass.Thom.IntersectionGeometry.isProperIntersectionCycle_unique X 1 (k + 1) hc (Supports.ProperCycle.intersectionBilinear_isProper X m 1 (k + 1) a b hc.1)
  have he' := CycleClass.Thom.IntersectionGeometry.isProperIntersectionCycle_unique X 1 (k + 1) hc' (Supports.ProperCycle.intersectionBilinear_isProper X m 1 (k + 1) a' b' hc'.1)
  rw [he, he']
  exact intersection_congr X m k a a' b b' ha hb hc.1 hc'.1

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.DivisorDescent
