import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.LeftDescent
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Symmetry

/-! # Descent -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.Descent

noncomputable section

/-! Proper divisor intersections on an integral smooth presentation
are independent of both rationally equivalent representatives. -/

open _root_.AlgebraicGeometry
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Symmetry

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
  [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]

include m

theorem intersection_congr_right (a b b' : X.RationalDimensionCycle 1)
    (hb : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 b b') (hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 1 a b)
    (hp' : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 1 a b') :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 2 (Supports.ProperCycle.intersectionBilinear X m 1 1 a b)
      (Supports.ProperCycle.intersectionBilinear X m 1 1 a b') := by
  rw [Symmetry.bilinear_comm X m a b, Symmetry.bilinear_comm X m a b']
  exact LeftDescent.intersection_congr_left X m b b' a hb
    ((Symmetry.meetProperly_comm X a b).mp hp) ((Symmetry.meetProperly_comm X a b').mp hp')

theorem intersection_congr (a a' b b' : X.RationalDimensionCycle 1)
    (ha : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 a a') (hb : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 b b')
    (hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 1 a b) (hp' : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 1 a' b') :
    CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 2 (Supports.ProperCycle.intersectionBilinear X m 1 1 a b)
      (Supports.ProperCycle.intersectionBilinear X m 1 1 a' b') := by
  obtain ⟨u, hau, havoid⟩ := ChowMoving.exists_rationallyEquivalent_avoiding X m
    (b.support ∪ b'.support) a
  have hub : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 1 u b := ChowMoving.meetProperly_of_avoiding X m u b
    (fun B hB => havoid B (Finset.mem_union_left _ hB))
  have hub' : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 1 u b' := ChowMoving.meetProperly_of_avoiding X m u b'
    (fun B hB => havoid B (Finset.mem_union_right _ hB))
  have hua' : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 u a' :=
    CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X 1 (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_symm X 1 hau) ha
  exact CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X 2
    (LeftDescent.intersection_congr_left X m a u b hau hp hub)
    (CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_trans X 2 (intersection_congr_right X m u b b' hb hub hub')
      (LeftDescent.intersection_congr_left X m u a' b' hua' hub' hp'))

theorem proper_intersections_congr (a a' b b' : X.RationalDimensionCycle 1)
    (ha : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 a a') (hb : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 b b')
    (c c' : X.RationalDimensionCycle 2)
    (hc : CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X 1 1 a b c)
    (hc' : CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X 1 1 a' b' c') : CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 2 c c' := by
  have he := CycleClass.Thom.IntersectionGeometry.isProperIntersectionCycle_unique X 1 1 hc
    (Supports.ProperCycle.intersectionBilinear_isProper X m 1 1 a b hc.1)
  have he' := CycleClass.Thom.IntersectionGeometry.isProperIntersectionCycle_unique X 1 1 hc'
    (Supports.ProperCycle.intersectionBilinear_isProper X m 1 1 a' b' hc'.1)
  rw [he, he']
  exact intersection_congr X m a a' b b' ha hb hc.1 hc'.1

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.Descent
