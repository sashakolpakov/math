import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Cycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Principal
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.ComponentFactor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Bilinear

/-! # Cycle Components -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.CycleComponents

noncomputable section

/-! Component restriction and target factorization of smooth inverse-image cycles
in every codimension. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Cycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.ComponentFactor

theorem restrict_flatMap {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
    (m n p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    [SmoothOfRelativeDimension n Y.structureMap]
    (C : irreducibleComponents X.carrier) (a : Y.RationalDimensionCycle p) :
    Component.CycleMaps.restrict X C p (Cycle.flatMap f p a) = Cycle.flatMap (Component.Image.inclusion X C ≫ f) p a := by
  let : SmoothOfRelativeDimension m (X.componentVariety C).structureMap := Component.Image.component_relativeDimension X m C
  let : Smooth (Component.Image.inclusion X C ≫ f).left := by
    change Smooth (X.componentInclusion C ≫ f.left)
    infer_instance
  ext A
  rw [Component.CycleMaps.restrict_apply, Cycle.flatMap_apply f p m n, Cycle.flatMap_apply (Component.Image.inclusion X C ≫ f) p m n]
  have he : f.left (CycleClass.Thom.IntersectionGeometry.supportPoint (Component.Image.supportImage X C p A).val) =
      (Component.Image.inclusion X C ≫ f).left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) := by
    rw [Component.Image.supportImage_point]
    rfl
  exact congrArg (fun y : Y.carrier => a.sum (fun B r => r * if y = CycleClass.Thom.IntersectionGeometry.supportPoint B.val then 1 else 0)) he

theorem flatMap_factor {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral X.carrier]
    (g : X.toOver ⟶ Y.toOver) [Smooth g.left]
    (m n p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    [SmoothOfRelativeDimension n Y.structureMap] (a : Y.RationalDimensionCycle p) :
    Cycle.flatMap g p a = Cycle.flatMap (Integral.ComponentFactor.overMap Y g) p (Component.CycleMaps.restrict Y (Integral.ComponentFactor.component (Z := X.carrier) Y g.left) p a) := by
  let D := Integral.ComponentFactor.component (Z := X.carrier) Y g.left
  let : SmoothOfRelativeDimension n (Y.componentVariety D).structureMap := Component.Image.component_relativeDimension Y n D
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single B r =>
    by_cases hB : (B.val : Set Y.carrier) ⊆ D.val
    · obtain ⟨B', rfl⟩ : ∃ B', Component.Image.supportImage Y D p B' = B :=
        ⟨Component.Image.supportPreimage Y D p B hB, Component.Image.supportImage_preimage Y D p B hB⟩
      rw [Component.Bilinear.restrict_single_image]
      change (Finsupp.linearCombination ℚ (Cycle.cycle g p)) (Finsupp.single _ r) =
        (Finsupp.linearCombination ℚ (Cycle.cycle (Integral.ComponentFactor.overMap Y g) p)) (Finsupp.single B' r)
      rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single]
      ext A
      rw [Finsupp.smul_apply, Finsupp.smul_apply, Cycle.cycle_apply g p m n, Cycle.cycle_apply (Integral.ComponentFactor.overMap Y g) p m n]
      have hf : g.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = Y.componentInclusion D ((Integral.ComponentFactor.overMap Y g).left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val)) :=
        (congrArg (fun h : X.carrier ⟶ Y.carrier => h (CycleClass.Thom.IntersectionGeometry.supportPoint A.val)) (Integral.ComponentFactor.fac (Z := X.carrier) Y g.left)).symm
      have hb := Component.Image.supportImage_point Y D p B'
      have he : g.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint (Component.Image.supportImage Y D p B').val ↔
          (Integral.ComponentFactor.overMap Y g).left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B'.val := by
        rw [hf, hb]
        exact (Y.componentInclusion D).isOpenEmbedding.injective.eq_iff
      simp only [he]
    · rw [Component.Bilinear.restrict_single_outside Y D p B r hB, map_zero]
      change (Finsupp.linearCombination ℚ (Cycle.cycle g p)) (Finsupp.single B r) = 0
      rw [Finsupp.linearCombination_single]
      ext A
      rw [Finsupp.smul_apply, Cycle.cycle_apply g p m n, Finsupp.zero_apply]
      have hn : g.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) ≠ CycleClass.Thom.IntersectionGeometry.supportPoint B.val := by
        intro he
        have hd : g.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) ∈ D.val :=
          Y.support_subset_component (CycleClass.Geometric.StratumClosure.integralImageClosure (Y := X.carrier) (X := Y.carrier) g.left)
            (subset_closure (Set.mem_range_self _))
        exact hB (Component.Principal.subset_of_mem Y D B.val (CycleClass.Thom.IntersectionGeometry.supportPoint B.val)
          ((B.val.isIrreducible.isGenericPoint_genericPoint B.val.isClosed).mem) (he ▸ hd))
      rw [ite_eq_right hn, smul_zero]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.CycleComponents
