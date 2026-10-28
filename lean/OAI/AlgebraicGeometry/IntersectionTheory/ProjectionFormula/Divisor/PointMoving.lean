import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.DivisorPointMoving
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CycleMaps

/-! # Point Moving -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.PointMoving

noncomputable section

/-! Divisors on every smooth projective scheme can be moved away
from any finite set of points, including points on different components. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CycleMaps

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]

include m

theorem move_single (S : Finset X.carrier) (A : X.DimensionCycleSupport 1) :
    ∃ b : X.RationalDimensionCycle 1, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 (Finsupp.single A 1) b ∧
      ∀ B ∈ b.support, ∀ x ∈ S, x ∉ (B.val : Set X.carrier) := by
  let C := X.supportComponent A.val
  let V := (X.componentVariety C).presentation
  let : SmoothOfRelativeDimension m V.structureMap := Component.Image.component_relativeDimension X m C
  let A' := Component.Image.supportPreimage X C 1 A (X.support_subset_component A.val)
  let T := S.preimage (X.componentInclusion C) (X.componentInclusion C).isEmbedding.injective.injOn
  obtain ⟨b, hb, hs⟩ := Integral.DivisorPointMoving.move_single V m T A'
  refine ⟨Component.CycleMaps.embed X C 1 b, ?_, ?_⟩
  · have he := Component.CycleMaps.embed_preserves_relations X m C 1 hb
    change Component.CycleMaps.embed X C 1 (Finsupp.single A' 1 - b) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1 at he
    rw [map_sub, Component.CycleMaps.embed_single, Component.Image.supportImage_preimage] at he
    exact he
  · intro B hB x hx hxB
    have hBn : Finsupp.mapDomain (Component.Image.supportImage X C 1) b B ≠ 0 := Finsupp.mem_support_iff.mp hB
    obtain ⟨B', rfl⟩ := Finsupp.mem_range_of_mapDomain_ne_zero hBn
    have hB' : B' ∈ b.support := by
      apply Finsupp.mem_support_iff.mpr
      simpa only [Finsupp.mapDomain_apply_of_injective (Component.Image.supportImage_injective X C 1)] using hBn
    obtain ⟨y, hy, he⟩ := hxB
    have hyT : y ∈ T := by
      apply Finset.mem_preimage.mpr
      exact he ▸ hx
    exact hs B' hB' y hyT hy

theorem move (S : Finset X.carrier) (a : X.RationalDimensionCycle 1) :
    ∃ b : X.RationalDimensionCycle 1, CycleClass.Thom.IntersectionGeometry.RationallyEquivalent X 1 a b ∧
      ∀ B ∈ b.support, ∀ x ∈ S, x ∉ (B.val : Set X.carrier) := by
  induction a using Finsupp.induction_linear with
  | zero =>
    refine ⟨0, CycleClass.Thom.IntersectionGeometry.rationallyEquivalent_refl X 1 0, ?_⟩
    intro B hB
    simp at hB
  | add a b ha hb =>
    obtain ⟨a', ha', hsa⟩ := ha
    obtain ⟨b', hb', hsb⟩ := hb
    refine ⟨a' + b', ?_, ?_⟩
    · change (a + b) - (a' + b') ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1
      have he : (a + b) - (a' + b') = (a - a') + (b - b') := by abel
      rw [he]
      exact Submodule.add_mem _ ha' hb'
    · intro B hB x hx
      rcases Finset.mem_union.mp (Finsupp.support_add hB) with hB | hB
      · exact hsa B hB x hx
      · exact hsb B hB x hx
  | single A r =>
    obtain ⟨b, hb, hs⟩ := move_single X m S A
    refine ⟨r • b, ?_, fun B hB x hx => hs B (Finsupp.support_smul hB) x hx⟩
    change Finsupp.single A r - r • b ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1
    have hr : Finsupp.single A r = r • Finsupp.single A (1 : ℚ) := by simp
    rw [hr, ← smul_sub]
    exact Submodule.smul_mem _ r hb

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.PointMoving
