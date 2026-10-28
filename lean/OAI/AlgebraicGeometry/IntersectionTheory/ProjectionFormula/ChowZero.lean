import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Action
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DegreeCast

/-! # Chow Zero -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowZero

noncomputable section

/-! The exact geometric intersection relation is the graph of a bilinear
map whenever the first input has codimension zero. No moving premise is
needed in this degree: every pair already meets properly. -/

set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical BigOperators

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Action

def cycleIntersection (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (q : ℕ) :
    X.RationalDimensionCycle 0 →ₗ[ℚ] X.RationalDimensionCycle q →ₗ[ℚ]
      X.RationalDimensionCycle (0 + q) :=
  (Component.Action.cycleAction X q).compr₂ (DegreeCast.cycle X (Nat.zero_add q).symm).toLinearMap

theorem cycleIntersection_isProper (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a : X.RationalDimensionCycle 0) (b : X.RationalDimensionCycle q) :
    CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X 0 q a b (cycleIntersection X q a b) := by
  refine ⟨IntersectionZero.meetProperly_zero_left X m q a b, ?_⟩
  intro C
  let D : X.DimensionCycleSupport q := ⟨C.val, C.property.trans (Nat.zero_add q)⟩
  change DegreeCast.cycle X (Nat.zero_add q).symm (Component.Action.cycleAction X q a b) C = _
  rw [DegreeCast.cycle_apply, Component.Action.cycleAction_apply]
  apply Finset.sum_congr rfl
  intro A _
  change _ = ∑ B ∈ b.support, a A * b B * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A.val B.val D.val
  simp only [IntersectionZero.multiplicity_zero_left X m q]
  change a A * (if D.val ≤ A.val then b D else 0) = _
  by_cases hD : D.val ≤ A.val
  · simp only [hD, and_true, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
    by_cases hb : D ∈ b.support
    · simp [hb]
    · have hz : b D = 0 := Finsupp.notMem_support_iff.mp hb
      simp [hb, hz]
  · simp [hD]

def chowActionOnCycles (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] :
    X.RationalDimensionCycle 0 →ₗ[ℚ] ProperCycleLinearity.ChowQ X q →ₗ[ℚ] ProperCycleLinearity.ChowQ X q where
  toFun a := (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X q).mapQ (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X q)
    (Component.Action.cycleAction X q a) (Component.Action.cycleAction_preserves_relations X m q a)
  map_add' a b := by
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X q z
    change ProperCycleLinearity.cycleToChowQ X q (Component.Action.cycleAction X q (a + b) z) =
      ProperCycleLinearity.cycleToChowQ X q (Component.Action.cycleAction X q a z) + ProperCycleLinearity.cycleToChowQ X q (Component.Action.cycleAction X q b z)
    simp only [map_add, LinearMap.add_apply]
  map_smul' r a := by
    apply LinearMap.ext
    intro z
    obtain ⟨z, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X q z
    change ProperCycleLinearity.cycleToChowQ X q (Component.Action.cycleAction X q (r • a) z) =
      r • ProperCycleLinearity.cycleToChowQ X q (Component.Action.cycleAction X q a z)
    simp only [map_smul, LinearMap.smul_apply]

def chowAction (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] :
    ProperCycleLinearity.ChowQ X 0 →ₗ[ℚ] ProperCycleLinearity.ChowQ X q →ₗ[ℚ] ProperCycleLinearity.ChowQ X q :=
  (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 0).liftQ (chowActionOnCycles X m q) (by
    rw [Component.Action.rationalEquivalences_zero]
    exact bot_le)

def chowIntersectionMap (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] :
    ProperCycleLinearity.ChowQ X 0 →ₗ[ℚ] ProperCycleLinearity.ChowQ X q →ₗ[ℚ] ProperCycleLinearity.ChowQ X (0 + q) :=
  (chowAction X m q).compr₂ (DegreeCast.chow X (Nat.zero_add q).symm).toLinearMap

theorem chowIntersectionMap_mk (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a : X.RationalDimensionCycle 0) (b : X.RationalDimensionCycle q) :
    chowIntersectionMap X m q (ProperCycleLinearity.cycleToChowQ X 0 a) (ProperCycleLinearity.cycleToChowQ X q b) =
      ProperCycleLinearity.cycleToChowQ X (0 + q) (cycleIntersection X q a b) := by
  exact DegreeCast.chow_mk X (Nat.zero_add q).symm (Component.Action.cycleAction X q a b)

theorem representsIntersection_iff (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (a : X.RationalDimensionCycle 0) (b : X.RationalDimensionCycle q)
    (c : X.RationalDimensionCycle (0 + q)) :
    CycleClass.Thom.IntersectionGeometry.RepresentsIntersection X 0 q a b c ↔
      ProperCycleLinearity.cycleToChowQ X (0 + q) c =
        chowIntersectionMap X m q (ProperCycleLinearity.cycleToChowQ X 0 a) (ProperCycleLinearity.cycleToChowQ X q b) := by
  constructor
  · rintro ⟨a', b', c', ha, hb, hp, hc⟩
    rw [(ProperCycleLinearity.cycleToChowQ_eq_iff X 0 a a').mpr ha,
      (ProperCycleLinearity.cycleToChowQ_eq_iff X q b b').mpr hb, chowIntersectionMap_mk,
      (ProperCycleLinearity.cycleToChowQ_eq_iff X (0 + q) c c').mpr hc]
    exact congrArg (ProperCycleLinearity.cycleToChowQ X (0 + q))
      (CycleClass.Thom.IntersectionGeometry.isProperIntersectionCycle_unique X 0 q hp (cycleIntersection_isProper X m q a' b'))
  · intro h
    refine ⟨a, b, cycleIntersection X q a b, CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X 0 a,
      CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X q b, cycleIntersection_isProper X m q a b, ?_⟩
    apply (ProperCycleLinearity.cycleToChowQ_eq_iff X (0 + q) c (cycleIntersection X q a b)).mp
    exact h.trans (chowIntersectionMap_mk X m q a b)

theorem chowIntersection_eq_singleton (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (a : ProperCycleLinearity.ChowQ X 0) (b : ProperCycleLinearity.ChowQ X q) :
    ProperCycleLinearity.chowIntersection X 0 q a b = {chowIntersectionMap X m q a b} := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X 0 a
  obtain ⟨b, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X q b
  ext c
  obtain ⟨c, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective X (0 + q) c
  rw [ProperCycleLinearity.chowIntersection_mk_iff, Set.mem_singleton_iff, representsIntersection_iff X m q]

theorem chowIntersection_map_exists (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] :
    ∃ I : ProperCycleLinearity.ChowQ X 0 →ₗ[ℚ] ProperCycleLinearity.ChowQ X q →ₗ[ℚ] ProperCycleLinearity.ChowQ X (0 + q),
      ∀ a b, ProperCycleLinearity.chowIntersection X 0 q a b = {I a b} :=
  ⟨chowIntersectionMap X m q, chowIntersection_eq_singleton X m q⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowZero
