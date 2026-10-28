import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Bilinear
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.DivisorCycle

/-! # Smooth Target -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.SmoothTarget

noncomputable section

/-! Smooth divisor pullback through a map factoring through an open
and closed target part uses exactly the restricted divisor cycle. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveFiberCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Cycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Bilinear

theorem factor {X V Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (i : V.toOver ⟶ Y.toOver) [IsOpenImmersion i.left] [IsClosedImmersion i.left]
    (f : X.toOver ⟶ V.toOver) [Smooth f.left]
    (m n : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    [SmoothOfRelativeDimension n V.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
    (a : Y.RationalDimensionCycle 1) :
    CurveFiberCycle.flatMap (f ≫ i) a = CurveFiberCycle.flatMap f (CycleMaps.restrict i n 1 a) := by
  let : Smooth (f ≫ i).left := by
    change Smooth (f.left ≫ i.left)
    infer_instance
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single B r =>
    by_cases hB : (B.val : Set Y.carrier) ⊆ Set.range i.left
    · obtain ⟨B', rfl⟩ : ∃ B', Cycle.supportImage i n 1 B' = B :=
        ⟨Cycle.supportPreimage i n 1 B hB, Cycle.supportImage_preimage i n 1 B hB⟩
      rw [Bilinear.restrict_single_image]
      change (Finsupp.linearCombination ℚ (CurveFiberCycle.cycle (f ≫ i))) (Finsupp.single _ r) =
        (Finsupp.linearCombination ℚ (CurveFiberCycle.cycle f)) (Finsupp.single B' r)
      rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single]
      ext A
      rw [Finsupp.smul_apply, Finsupp.smul_apply,
        ProjectionFormula.Smooth.DivisorCycle.cycle_apply (f ≫ i) m n, ProjectionFormula.Smooth.DivisorCycle.cycle_apply f m n]
      have he : (f ≫ i).left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint (Cycle.supportImage i n 1 B').val ↔
          f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B'.val := by
        change i.left (f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val)) =
          CycleClass.Thom.IntersectionGeometry.supportPoint (ProperCycleLinearity.imageSupport i B'.val) ↔ _
        rw [Cycle.image_point]
        exact i.left.isOpenEmbedding.injective.eq_iff
      simp only [he]
    · rw [Bilinear.restrict_single_outside i n 1 B r hB, map_zero]
      change (Finsupp.linearCombination ℚ (CurveFiberCycle.cycle (f ≫ i))) (Finsupp.single B r) = 0
      rw [Finsupp.linearCombination_single]
      ext A
      rw [Finsupp.smul_apply, ProjectionFormula.Smooth.DivisorCycle.cycle_apply (f ≫ i) m n, Finsupp.zero_apply]
      have hn : (f ≫ i).left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) ≠ CycleClass.Thom.IntersectionGeometry.supportPoint B.val := by
        intro he
        have hr : CycleClass.Thom.IntersectionGeometry.supportPoint B.val ∈ Set.range i.left := by
          rw [← he]
          exact Set.mem_range_self _
        exact hB (Cycle.subset_range_of_mem i B.val (CycleClass.Thom.IntersectionGeometry.supportPoint B.val)
          (B.val.isIrreducible.isGenericPoint_genericPoint B.val.isClosed).mem hr)
      rw [ite_eq_right hn, smul_zero]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.SmoothTarget
