import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveFlatDescent
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Bilinear

/-! # Curve Flat Components -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveFlatComponents

noncomputable section

/-! Smooth divisor pullback only uses the target component reached by
an integral source. This proves descent for disconnected curve targets. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveFiberCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.ComponentFactor

theorem flatMap_factor {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral X.carrier]
    [SmoothOfRelativeDimension 1 Y.structureMap] (g : X.toOver ⟶ Y.toOver) [Smooth g.left]
    (m : ℕ) [SmoothOfRelativeDimension m X.structureMap] (a : Y.RationalDimensionCycle 1) :
    CurveFiberCycle.flatMap g a = CurveFiberCycle.flatMap (Integral.ComponentFactor.overMap Y g) (Component.CycleMaps.restrict Y (Integral.ComponentFactor.component (Z := X.carrier) Y g.left) 1 a) := by
  let D := Integral.ComponentFactor.component (Z := X.carrier) Y g.left
  let : SmoothOfRelativeDimension 1 (Y.componentVariety D).structureMap := Component.Image.component_relativeDimension Y 1 D
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single B r =>
    by_cases hB : (B.val : Set Y.carrier) ⊆ D.val
    · obtain ⟨B', rfl⟩ : ∃ B', Component.Image.supportImage Y D 1 B' = B :=
        ⟨Component.Image.supportPreimage Y D 1 B hB, Component.Image.supportImage_preimage Y D 1 B hB⟩
      rw [Component.Bilinear.restrict_single_image]
      change (Finsupp.linearCombination ℚ (CurveFiberCycle.cycle g)) (Finsupp.single _ r) =
        (Finsupp.linearCombination ℚ (CurveFiberCycle.cycle (Integral.ComponentFactor.overMap Y g))) (Finsupp.single B' r)
      rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single]
      ext A
      rw [Finsupp.smul_apply, Finsupp.smul_apply, CurveFiberCycle.cycle_apply g m, CurveFiberCycle.cycle_apply (Integral.ComponentFactor.overMap Y g) m]
      have hf : g.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = Y.componentInclusion D ((Integral.ComponentFactor.overMap Y g).left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val)) :=
        (congrArg (fun h : X.carrier ⟶ Y.carrier => h (CycleClass.Thom.IntersectionGeometry.supportPoint A.val)) (Integral.ComponentFactor.fac (Z := X.carrier) Y g.left)).symm
      have hb := Component.Image.supportImage_point Y D 1 B'
      have he : g.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint (Component.Image.supportImage Y D 1 B').val ↔
          (Integral.ComponentFactor.overMap Y g).left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B'.val := by
        rw [hf, hb]
        exact (Y.componentInclusion D).isOpenEmbedding.injective.eq_iff
      simp only [he]
    · rw [Component.Bilinear.restrict_single_outside Y D 1 B r hB, map_zero]
      change (Finsupp.linearCombination ℚ (CurveFiberCycle.cycle g)) (Finsupp.single B r) = 0
      rw [Finsupp.linearCombination_single]
      ext A
      rw [Finsupp.smul_apply, CurveFiberCycle.cycle_apply g m, Finsupp.zero_apply]
      have hn : g.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) ≠ CycleClass.Thom.IntersectionGeometry.supportPoint B.val := by
        intro he
        have hd : g.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) ∈ D.val :=
          Y.support_subset_component (CycleClass.Geometric.StratumClosure.integralImageClosure (Y := X.carrier) (X := Y.carrier) g.left)
            (subset_closure (Set.mem_range_self _))
        exact hB (Component.Principal.subset_of_mem Y D B.val (CycleClass.Thom.IntersectionGeometry.supportPoint B.val)
          ((B.val.isIrreducible.isGenericPoint_genericPoint B.val.isClosed).mem) (he ▸ hd))
      rw [ite_eq_right hn, smul_zero]

theorem flatMap_preserves_relations {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    [SmoothOfRelativeDimension 1 Y.structureMap] (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
    (m : ℕ) [SmoothOfRelativeDimension m X.structureMap] :
    CycleClass.Thom.IntersectionGeometry.rationalEquivalences Y 1 ≤ (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1).comap (CurveFiberCycle.flatMap f) := by
  intro a ha
  apply (Component.Principal.CycleDecomposition.relations_iff X m 1 (CurveFiberCycle.flatMap f a)).mpr
  intro C
  let V := (X.componentVariety C).presentation
  let g : V.toOver ⟶ Y.toOver := Component.Image.inclusion X C ≫ f
  let D := Integral.ComponentFactor.component (Z := V.carrier) Y g.left
  let : SmoothOfRelativeDimension m V.structureMap := Component.Image.component_relativeDimension X m C
  let : SmoothOfRelativeDimension 1 (Y.componentVariety D).structureMap := Component.Image.component_relativeDimension Y 1 D
  let : Smooth g.left := by
    change Smooth (X.componentInclusion C ≫ f.left)
    infer_instance
  rw [CurveFlatDescent.restrict_flatMap f m C, flatMap_factor g m a]
  exact CurveFlatPrincipal.flatMap_preserves_relations (Integral.ComponentFactor.overMap Y g) m
    (Component.Principal.restrict_preserves_relations Y D 1 ha)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveFlatComponents
