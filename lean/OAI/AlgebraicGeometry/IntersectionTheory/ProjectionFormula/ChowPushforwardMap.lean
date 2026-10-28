import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PushforwardDescent

/-! # Chow Pushforward Map -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardMap

noncomputable section

/-! The proved proper pushforward relation, packaged as its unique linear
map with its action on actual cycle representatives. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
  (m n p q : ℕ) [SmoothOfRelativeDimension m X.structureMap]
  [SmoothOfRelativeDimension n Y.structureMap] (hdeg : p + n = q + m)

def map : ProperCycleLinearity.ChowQ X p →ₗ[ℚ] ProperCycleLinearity.ChowQ Y q :=
  Classical.choose (PushforwardDescent.chowPushforward_map_exists f m n p q hdeg)

theorem graph (a : ProperCycleLinearity.ChowQ X p) : ProperCycleLinearity.chowPushforward f p q a = {map f m n p q hdeg a} :=
  Classical.choose_spec (PushforwardDescent.chowPushforward_map_exists f m n p q hdeg) a

theorem map_mk (a : X.RationalDimensionCycle p) :
    map f m n p q hdeg (ProperCycleLinearity.cycleToChowQ X p a) = ProperCycleLinearity.cycleToChowQ Y q (ProperCycleLinearity.cyclePushforward f p q a) := by
  have h : ProperCycleLinearity.cycleToChowQ Y q (ProperCycleLinearity.cyclePushforward f p q a) ∈
      ProperCycleLinearity.chowPushforward f p q (ProperCycleLinearity.cycleToChowQ X p a) := ⟨a, rfl, rfl⟩
  rw [graph f m n p q hdeg] at h
  exact (Set.mem_singleton_iff.mp h).symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardMap
