import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.Support
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardCast
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowPullback

/-! # Graph Pullback Reconstruction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GraphPullbackReconstruction

noncomputable section

/-! The defining graph intersection is exactly the graph pushforward
of the constructed Chow pullback, including disconnected schemes. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.GeneralChowIntersection OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardMap

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y)
  (f : X.toOver ⟶ Y.toOver) (m n : ℕ)
  [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]

local instance : SmoothOfRelativeDimension (m + n) P.space.structureMap :=
  ProductDimension.relativeDimension P m n

theorem intersection_eq (p : ℕ) (a : ProperCycleLinearity.ChowQ P.space n) (b : ProperCycleLinearity.ChowQ P.space p) :
    General.PullbackOnCycles.intersection P m n p a b = General.GeneralChowIntersection.chowMap P.space (m + n) n p a b := by
  have h := General.PullbackOnCycles.intersection_spec P m n p a b
  rw [General.GeneralChowIntersection.chowIntersection_eq_singleton P.space (m + n) n p a b] at h
  exact (Set.singleton_injective h).symm

theorem image (p : ℕ) (b : ProperCycleLinearity.ChowQ P.space p) :
    ∃ c : ProperCycleLinearity.ChowQ X p, ChowPushforwardMap.map (P.graph f) m (m + n) p (n + p) (by omega) c =
      General.GeneralChowIntersection.chowMap P.space (m + n) n p (ProperCycleLinearity.cycleToChowQ P.space n (P.graphCycle f n)) b := by
  have hi (t : ℕ) (ht : 0 + n = t) : ∃ c : ProperCycleLinearity.ChowQ X p,
      ChowPushforwardMap.map (P.graph f) m (m + n) p (p + t) (by omega) c =
        General.GeneralChowIntersection.chowMap P.space (m + n) p t b
          (ChowPushforwardMap.map (P.graph f) m (m + n) 0 t (by omega) (ProperCycleLinearity.cycleToChowQ X 0 (ProperCycleLinearity.fundamentalCycle X))) := by
    subst t
    exact Closed.Support.image (P.graph f) m (m + n) n rfl p 0 b
      (ProperCycleLinearity.cycleToChowQ X 0 (ProperCycleLinearity.fundamentalCycle X))
  obtain ⟨c, hc⟩ := hi n (Nat.zero_add n)
  have hc' : ChowPushforwardMap.map (P.graph f) m (m + n) p (p + n) (by omega) c =
      General.GeneralChowIntersection.chowMap P.space (m + n) p n b (ProperCycleLinearity.cycleToChowQ P.space n (P.graphCycle f n)) := by
    rw [ChowPushforwardMap.map_mk] at hc
    exact hc
  refine ⟨c, ?_⟩
  calc
    _ = DegreeCast.chow P.space (Nat.add_comm p n)
        (ChowPushforwardMap.map (P.graph f) m (m + n) p (p + n) (by omega) c) :=
      (ChowPushforwardCast.target (P.graph f) m (m + n) p (p + n) (n + p)
        (Nat.add_comm p n) (by omega) (by omega) c).symm
    _ = _ := by rw [hc', General.ChowAssociativity.comm]

theorem reconstruct (p : ℕ) (b : ProperCycleLinearity.ChowQ P.space p) :
    ChowPushforwardMap.map (P.graph f) m (m + n) p (n + p) (by omega)
      (ChowPushforwardMap.map P.fst (m + n) m (n + p) p (by omega)
        (General.GeneralChowIntersection.chowMap P.space (m + n) n p (ProperCycleLinearity.cycleToChowQ P.space n (P.graphCycle f n)) b)) =
    General.GeneralChowIntersection.chowMap P.space (m + n) n p (ProperCycleLinearity.cycleToChowQ P.space n (P.graphCycle f n)) b := by
  obtain ⟨c, hc⟩ := image P f m n p b
  rw [← hc, ChowPushforwardComposition.comp (P.graph f) P.fst m (m + n) m p (n + p) p
    (by omega) (by omega) rfl c, P.graph_fst f, Closed.Support.pushforward_id]

theorem graph_push_pull (p : ℕ) (a : Y.RationalDimensionCycle p) :
    ChowPushforwardMap.map (P.graph f) m (m + n) p (n + p) (by omega)
      (General.ChowPullback.pull P f m n p (ProperCycleLinearity.cycleToChowQ Y p a)) =
    General.GeneralChowIntersection.chowMap P.space (m + n) n p (ProperCycleLinearity.cycleToChowQ P.space n (P.graphCycle f n))
      (ProperCycleLinearity.cycleToChowQ P.space p (P.secondPullbackCycle p a)) := by
  rw [General.ChowPullback.pull_mk, General.PullbackOnCycles.onCycles_apply,
    intersection_eq P m n, reconstruct P f m n]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GraphPullbackReconstruction
