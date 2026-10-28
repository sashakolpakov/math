import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DegreeCast
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.GeneralChowIntersection
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductDimension

/-! # Pullback On Cycles -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.PullbackOnCycles

noncomputable section

/-! Exact graph pullback on cycles of arbitrary codimension for
arbitrary-dimensional source and target. The bilinear intersection is already proved from the
native geometric relation, including existence and independence. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y)
  (f : X.toOver ⟶ Y.toOver) (m n p : ℕ)
  [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]

local instance product_relativeDimension : SmoothOfRelativeDimension (m + n) P.space.structureMap :=
  ProductDimension.relativeDimension P m n

include m n

def intersection : ProperCycleLinearity.ChowQ P.space n →ₗ[ℚ] ProperCycleLinearity.ChowQ P.space p →ₗ[ℚ] ProperCycleLinearity.ChowQ P.space (n + p) :=
  (GeneralChowIntersection.chowIntersection_map_exists P.space (m + n) n p).choose

theorem intersection_spec (a : ProperCycleLinearity.ChowQ P.space n) (b : ProperCycleLinearity.ChowQ P.space p) :
    ProperCycleLinearity.chowIntersection P.space n p a b = {intersection P m n p a b} :=
  (GeneralChowIntersection.chowIntersection_map_exists P.space (m + n) n p).choose_spec a b

def onCycles : Y.RationalDimensionCycle p →ₗ[ℚ] ProperCycleLinearity.ChowQ X p :=
  (ChowPushforwardMap.map P.fst (m + n) m (n + p) p (by omega)).comp
    ((intersection P m n p (ProperCycleLinearity.cycleToChowQ P.space n (P.graphCycle f n))).comp
      ((ProperCycleLinearity.cycleToChowQ P.space p).comp (DegreeCast.ExteriorCycleLinear.secondPullbackMap P p)))

theorem onCycles_apply (a : Y.RationalDimensionCycle p) :
    onCycles P f m n p a = ChowPushforwardMap.map P.fst (m + n) m (n + p) p (by omega)
      (intersection P m n p (ProperCycleLinearity.cycleToChowQ P.space n (P.graphCycle f n))
        (ProperCycleLinearity.cycleToChowQ P.space p (P.secondPullbackCycle p a))) := by
  simp only [onCycles, LinearMap.comp_apply, DegreeCast.ExteriorCycleLinear.secondPullbackMap_apply]

theorem representsPullback_iff (a : Y.RationalDimensionCycle p) (b : X.RationalDimensionCycle p) :
    P.RepresentsPullback f n p a b ↔ ProperCycleLinearity.cycleToChowQ X p b = onCycles P f m n p a := by
  rw [onCycles_apply]
  constructor
  · rintro ⟨c, hc, hb⟩
    have hi := (ProperCycleLinearity.chowIntersection_mk_iff P.space n p _ _ c).mpr hc
    rw [intersection_spec P m n, Set.mem_singleton_iff] at hi
    rw [(ProperCycleLinearity.cycleToChowQ_eq_iff X p _ _).mpr hb,
      ← ChowPushforwardMap.map_mk P.fst (m + n) m (n + p) p (by omega), hi]
  · intro h
    obtain ⟨c, hc⟩ := ProperCycleLinearity.cycleToChowQ_surjective P.space (n + p)
      (intersection P m n p (ProperCycleLinearity.cycleToChowQ P.space n (P.graphCycle f n))
        (ProperCycleLinearity.cycleToChowQ P.space p (P.secondPullbackCycle p a)))
    refine ⟨c, ?_, ?_⟩
    · apply (ProperCycleLinearity.chowIntersection_mk_iff P.space n p _ _ c).mp
      rw [intersection_spec P m n, Set.mem_singleton_iff]
      exact hc
    · apply (ProperCycleLinearity.cycleToChowQ_eq_iff X p _ _).mp
      rw [← ChowPushforwardMap.map_mk P.fst (m + n) m (n + p) p (by omega), hc]
      exact h

theorem representsPullback_exists (a : Y.RationalDimensionCycle p) :
    ∃ b : X.RationalDimensionCycle p, P.RepresentsPullback f n p a b := by
  obtain ⟨b, hb⟩ := ProperCycleLinearity.cycleToChowQ_surjective X p (onCycles P f m n p a)
  exact ⟨b, (representsPullback_iff P f m n p a b).mpr hb⟩

theorem chowPullback_nonempty (a : ProperCycleLinearity.ChowQ Y p) : (ProperCycleLinearity.chowPullback P f n p a).Nonempty := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective Y p a
  obtain ⟨b, hb⟩ := representsPullback_exists P f m n p a
  exact ⟨ProperCycleLinearity.cycleToChowQ X p b, a, b, rfl, rfl, hb⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.PullbackOnCycles
