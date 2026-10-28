import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ProductCycleDescent
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.PullbackOnCycles

/-! # Chow Pullback -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowPullback

noncomputable section

/-! The exact linear graph pullback of Chow classes in every codimension for every
morphism of smooth projective presentations in all source and target dimensions. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.PullbackOnCycles

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y)
  (f : X.toOver ⟶ Y.toOver) (m n p : ℕ)
  [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]

include m n

theorem onCycles_relation (a : Y.RationalDimensionCycle p) (ha : a ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences Y p) :
    PullbackOnCycles.onCycles P f m n p a = 0 := by
  rw [PullbackOnCycles.onCycles_apply]
  have h := ProductCycleDescent.preserves_relations P m n p ha
  change DegreeCast.ExteriorCycleLinear.secondPullbackMap P p a ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences P.space p at h
  rw [DegreeCast.ExteriorCycleLinear.secondPullbackMap_apply] at h
  have he : ProperCycleLinearity.cycleToChowQ P.space p (P.secondPullbackCycle p a) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact h
  rw [he, map_zero, map_zero]

def pull : ProperCycleLinearity.ChowQ Y p →ₗ[ℚ] ProperCycleLinearity.ChowQ X p :=
  (CycleClass.Thom.IntersectionGeometry.rationalEquivalences Y p).liftQ (PullbackOnCycles.onCycles P f m n p) (onCycles_relation P f m n p)

theorem pull_mk (a : Y.RationalDimensionCycle p) :
    pull P f m n p (ProperCycleLinearity.cycleToChowQ Y p a) = PullbackOnCycles.onCycles P f m n p a := rfl

theorem chowPullback_eq_singleton (a : ProperCycleLinearity.ChowQ Y p) : ProperCycleLinearity.chowPullback P f n p a = {pull P f m n p a} := by
  ext b
  constructor
  · rintro ⟨z, w, hz, hw, hp⟩
    rw [Set.mem_singleton_iff, ← hw, ← hz, pull_mk]
    exact (PullbackOnCycles.representsPullback_iff P f m n p z w).mp hp
  · intro hb
    obtain ⟨z, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective Y p a
    obtain ⟨w, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X p b
    exact ⟨z, w, rfl, rfl, (PullbackOnCycles.representsPullback_iff P f m n p z w).mpr (Set.mem_singleton_iff.mp hb)⟩

theorem chowPullback_map_exists :
    ∃ F : ProperCycleLinearity.ChowQ Y p →ₗ[ℚ] ProperCycleLinearity.ChowQ X p, ∀ a, ProperCycleLinearity.chowPullback P f n p a = {F a} :=
  ⟨pull P f m n p, chowPullback_eq_singleton P f m n p⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowPullback
