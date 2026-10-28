import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ClopenCycles

/-! # Clopen Target -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ClopenTarget

noncomputable section

/-! Smooth inverse image through an open and closed target part uses
the restricted target cycle, in every codimension. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Cycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Cycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Bilinear

theorem factor {X V Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (i : V.toOver ⟶ Y.toOver) [IsOpenImmersion i.left] [IsClosedImmersion i.left]
    (f : X.toOver ⟶ V.toOver) [Smooth f.left]
    (m n p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    [SmoothOfRelativeDimension n V.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
    (a : Y.RationalDimensionCycle p) : ProjectionFormula.Smooth.Cycle.flatMap (f ≫ i) p a = ProjectionFormula.Smooth.Cycle.flatMap f p (Clopen.CycleMaps.restrict i n p a) := by
  let : Smooth (f ≫ i).left := by change Smooth (f.left ≫ i.left); infer_instance
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single B r =>
    by_cases hB : (B.val : Set Y.carrier) ⊆ Set.range i.left
    · obtain ⟨B', rfl⟩ : ∃ B', Clopen.Cycle.supportImage i n p B' = B :=
        ⟨Clopen.Cycle.supportPreimage i n p B hB, Clopen.Cycle.supportImage_preimage i n p B hB⟩
      rw [Clopen.Bilinear.restrict_single_image]
      change (Finsupp.linearCombination ℚ (ProjectionFormula.Smooth.Cycle.cycle (f ≫ i) p)) (Finsupp.single _ r) =
        (Finsupp.linearCombination ℚ (ProjectionFormula.Smooth.Cycle.cycle f p)) (Finsupp.single B' r)
      rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single]
      ext A
      rw [Finsupp.smul_apply, Finsupp.smul_apply,
        ProjectionFormula.Smooth.Cycle.cycle_apply (f ≫ i) p m n, ProjectionFormula.Smooth.Cycle.cycle_apply f p m n]
      have he : (f ≫ i).left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint (Clopen.Cycle.supportImage i n p B').val ↔
          f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B'.val := by
        change i.left (f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val)) = CycleClass.Thom.IntersectionGeometry.supportPoint (ProperCycleLinearity.imageSupport i B'.val) ↔ _
        rw [Clopen.Cycle.image_point]
        exact i.left.isOpenEmbedding.injective.eq_iff
      simp only [he]
    · rw [Clopen.Bilinear.restrict_single_outside i n p B r hB, map_zero]
      change (Finsupp.linearCombination ℚ (ProjectionFormula.Smooth.Cycle.cycle (f ≫ i) p)) (Finsupp.single B r) = 0
      rw [Finsupp.linearCombination_single]
      ext A
      rw [Finsupp.smul_apply, ProjectionFormula.Smooth.Cycle.cycle_apply (f ≫ i) p m n, Finsupp.zero_apply]
      have hn : (f ≫ i).left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) ≠ CycleClass.Thom.IntersectionGeometry.supportPoint B.val := by
        intro he
        have hr : CycleClass.Thom.IntersectionGeometry.supportPoint B.val ∈ Set.range i.left := by rw [← he]; exact Set.mem_range_self _
        exact hB (Clopen.Cycle.subset_range_of_mem i B.val (CycleClass.Thom.IntersectionGeometry.supportPoint B.val)
          (B.val.isIrreducible.isGenericPoint_genericPoint B.val.isClosed).mem hr)
      rw [ite_eq_right hn, smul_zero]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ClopenTarget
