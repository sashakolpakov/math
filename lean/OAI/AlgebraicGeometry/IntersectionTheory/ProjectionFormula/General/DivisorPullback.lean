import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ProductDivisorPullback
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.DivisorPullbackOnCycles

/-! # Divisor Pullback -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.DivisorPullback

noncomputable section

/-! The exact linear graph pullback of divisor Chow classes for every
morphism of smooth projective presentations in all source and target dimensions. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.DivisorPullbackOnCycles

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y)
  (f : X.toOver ⟶ Y.toOver) (m n : ℕ)
  [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]

include m n

theorem onCycles_relation (a : Y.RationalDimensionCycle 1) (ha : a ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences Y 1) :
    DivisorPullbackOnCycles.onCycles P f m n a = 0 := by
  rw [DivisorPullbackOnCycles.onCycles_apply]
  have h := ProductDivisorPullback.secondPullback_preserves_relations P m n ha
  change DegreeCast.ExteriorCycleLinear.secondPullbackMap P 1 a ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences P.space 1 at h
  rw [DegreeCast.ExteriorCycleLinear.secondPullbackMap_apply] at h
  have he : ProperCycleLinearity.cycleToChowQ P.space 1 (P.secondPullbackCycle 1 a) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact h
  rw [he, map_zero, map_zero]

def pull : ProperCycleLinearity.ChowQ Y 1 →ₗ[ℚ] ProperCycleLinearity.ChowQ X 1 :=
  (CycleClass.Thom.IntersectionGeometry.rationalEquivalences Y 1).liftQ (DivisorPullbackOnCycles.onCycles P f m n) (onCycles_relation P f m n)

theorem pull_mk (a : Y.RationalDimensionCycle 1) :
    pull P f m n (ProperCycleLinearity.cycleToChowQ Y 1 a) = DivisorPullbackOnCycles.onCycles P f m n a := rfl

theorem chowPullback_eq_singleton (a : ProperCycleLinearity.ChowQ Y 1) : ProperCycleLinearity.chowPullback P f n 1 a = {pull P f m n a} := by
  ext b
  constructor
  · rintro ⟨z, w, hz, hw, hp⟩
    rw [Set.mem_singleton_iff, ← hw, ← hz, pull_mk]
    exact (DivisorPullbackOnCycles.representsPullback_iff P f m n z w).mp hp
  · intro hb
    obtain ⟨z, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective Y 1 a
    obtain ⟨w, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X 1 b
    exact ⟨z, w, rfl, rfl, (DivisorPullbackOnCycles.representsPullback_iff P f m n z w).mpr (Set.mem_singleton_iff.mp hb)⟩

theorem chowPullback_map_exists :
    ∃ F : ProperCycleLinearity.ChowQ Y 1 →ₗ[ℚ] ProperCycleLinearity.ChowQ X 1, ∀ a, ProperCycleLinearity.chowPullback P f n 1 a = {F a} :=
  ⟨pull P f m n, chowPullback_eq_singleton P f m n⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.DivisorPullback
