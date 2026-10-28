import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DegreeCast
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.Divisor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductDimension

/-! # Divisor Pullback On Cycles -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.DivisorPullbackOnCycles

noncomputable section

/-! Exact graph pullback on divisor cycles for arbitrary-dimensional
source and target. The bilinear intersection is already proved from the
native geometric relation, including existence and independence. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y)
  (f : X.toOver ⟶ Y.toOver) (m n : ℕ)
  [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]

local instance product_relativeDimension : SmoothOfRelativeDimension (m + n) P.space.structureMap :=
  ProductDimension.relativeDimension P m n

include m n

def intersection : ProperCycleLinearity.ChowQ P.space n →ₗ[ℚ] ProperCycleLinearity.ChowQ P.space 1 →ₗ[ℚ] ProperCycleLinearity.ChowQ P.space (n + 1) :=
  (Divisor.right_map_exists P.space (m + n) n).choose

theorem intersection_spec (a : ProperCycleLinearity.ChowQ P.space n) (b : ProperCycleLinearity.ChowQ P.space 1) :
    ProperCycleLinearity.chowIntersection P.space n 1 a b = {intersection P m n a b} :=
  (Divisor.right_map_exists P.space (m + n) n).choose_spec a b

def onCycles : Y.RationalDimensionCycle 1 →ₗ[ℚ] ProperCycleLinearity.ChowQ X 1 :=
  (ChowPushforwardMap.map P.fst (m + n) m (n + 1) 1 (by omega)).comp
    ((intersection P m n (ProperCycleLinearity.cycleToChowQ P.space n (P.graphCycle f n))).comp
      ((ProperCycleLinearity.cycleToChowQ P.space 1).comp (DegreeCast.ExteriorCycleLinear.secondPullbackMap P 1)))

theorem onCycles_apply (a : Y.RationalDimensionCycle 1) :
    onCycles P f m n a = ChowPushforwardMap.map P.fst (m + n) m (n + 1) 1 (by omega)
      (intersection P m n (ProperCycleLinearity.cycleToChowQ P.space n (P.graphCycle f n))
        (ProperCycleLinearity.cycleToChowQ P.space 1 (P.secondPullbackCycle 1 a))) := by
  simp only [onCycles, LinearMap.comp_apply, DegreeCast.ExteriorCycleLinear.secondPullbackMap_apply]

theorem representsPullback_iff (a : Y.RationalDimensionCycle 1) (b : X.RationalDimensionCycle 1) :
    P.RepresentsPullback f n 1 a b ↔ ProperCycleLinearity.cycleToChowQ X 1 b = onCycles P f m n a := by
  rw [onCycles_apply]
  constructor
  · rintro ⟨c, hc, hb⟩
    have hi := (ProperCycleLinearity.chowIntersection_mk_iff P.space n 1 _ _ c).mpr hc
    rw [intersection_spec P m n, Set.mem_singleton_iff] at hi
    rw [(ProperCycleLinearity.cycleToChowQ_eq_iff X 1 _ _).mpr hb,
      ← ChowPushforwardMap.map_mk P.fst (m + n) m (n + 1) 1 (by omega), hi]
  · intro h
    obtain ⟨c, hc⟩ := ProperCycleLinearity.cycleToChowQ_surjective P.space (n + 1)
      (intersection P m n (ProperCycleLinearity.cycleToChowQ P.space n (P.graphCycle f n))
        (ProperCycleLinearity.cycleToChowQ P.space 1 (P.secondPullbackCycle 1 a)))
    refine ⟨c, ?_, ?_⟩
    · apply (ProperCycleLinearity.chowIntersection_mk_iff P.space n 1 _ _ c).mp
      rw [intersection_spec P m n, Set.mem_singleton_iff]
      exact hc
    · apply (ProperCycleLinearity.cycleToChowQ_eq_iff X 1 _ _).mp
      rw [← ChowPushforwardMap.map_mk P.fst (m + n) m (n + 1) 1 (by omega), hc]
      exact h

theorem representsPullback_exists (a : Y.RationalDimensionCycle 1) :
    ∃ b : X.RationalDimensionCycle 1, P.RepresentsPullback f n 1 a b := by
  obtain ⟨b, hb⟩ := ProperCycleLinearity.cycleToChowQ_surjective X 1 (onCycles P f m n a)
  exact ⟨b, (representsPullback_iff P f m n a b).mpr hb⟩

theorem chowPullback_nonempty (a : ProperCycleLinearity.ChowQ Y 1) : (ProperCycleLinearity.chowPullback P f n 1 a).Nonempty := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective Y 1 a
  obtain ⟨b, hb⟩ := representsPullback_exists P f m n a
  exact ⟨ProperCycleLinearity.cycleToChowQ X 1 b, a, b, rfl, rfl, hb⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.DivisorPullbackOnCycles
