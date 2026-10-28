import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.Pair
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.SectionCycles

/-! # Cycles -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.Cycles

noncomputable section

/-! The etale pair projection identity extends to every target
cycle in the chosen proper position. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.Map OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
  [GeometricallyIntegral (show X.carrier ⟶ Y.carrier from f.left)]
  (m n : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]

theorem support_injective (p : ℕ) : Function.Injective (Integral.FiberCycles.support f m n p) := by
  intro A B h
  apply Subtype.ext
  apply irreducibleSetEquivPoints.injective
  change CycleClass.Thom.IntersectionGeometry.supportPoint A.val = CycleClass.Thom.IntersectionGeometry.supportPoint B.val
  have he := congrArg (fun C : X.DimensionCycleSupport p => f.left (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)) h
  simp only [Integral.FiberCycles.support_point, Divisors.LineBundles.Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint_projection] at he
  exact he

theorem flat_support (p : ℕ) (a : Y.RationalDimensionCycle p) (A : Y.DimensionCycleSupport p)
    (hA : A ∈ a.support) : Integral.FiberCycles.support f m n p A ∈ (ProjectionFormula.Smooth.Cycle.flatMap f p a).support := by
  rw [ProjectionFormula.Smooth.SectionCycles.flatMap_eq_mapDomain f m n p a,
    Finsupp.mapDomain_support_of_injective (support_injective f m n p)]
  exact Finset.mem_image_of_mem _ hA

variable (p q s : ℕ) (hd : q + n = s + m) (a : Y.RationalDimensionCycle p)
  (W : X.DimensionCycleSupport q) (B : Y.DimensionCycleSupport s) (hB : ProperCycleLinearity.imageSupport f W.val = B.val)
  (hX : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q (ProjectionFormula.Smooth.Cycle.flatMap f p a) (Finsupp.single W 1))
  (hY : ∀ A ∈ a.support, Supports.ProperCycle.pairMeetsProperly Y p s A B)
  (U : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val).Opens) [Etale (U.ι ≫ Support.Map.supportImageMap f W.val)]
  (hgood : ∀ A ∈ a.support, ∀ D : Y.DimensionCycleSupport (p + s),
    CycleClass.Thom.IntersectionGeometry.supportPoint D.val ∈ (A.val : Set Y.carrier) →
    ∀ hDW : CycleClass.Thom.IntersectionGeometry.supportPoint D.val ∈ (ProperCycleLinearity.imageSupport f W.val : Set Y.carrier),
      CycleClass.Thom.IntersectionGeometry.supportPreimage (ProperCycleLinearity.imageSupport f W.val) (CycleClass.Thom.IntersectionGeometry.supportPoint D.val) hDW ∈
        Proper.EtaleRestriction.good (Support.Map.supportImageMap f W.val) U)

include hB in
omit [Smooth f.left] [GeometricallyIntegral (show X.carrier ⟶ Y.carrier from f.left)]
  [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
  [Etale (U.ι ≫ Support.Map.supportImageMap f W.val)] in
theorem push_single : ProperCycleLinearity.cyclePushforward f q s (Finsupp.single W 1) =
    (f.left.residueDegree (CycleClass.Thom.IntersectionGeometry.supportPoint W.val) : ℚ) • Finsupp.single B 1 := by
  rw [ProperCycleLinearity.cyclePushforward_single, one_smul, ProperCycleLinearity.cyclePushforwardGenerator, hB, CycleClass.Thom.IntersectionGeometry.supportInDegree, dite_eq_left B.property]
  rfl

include hB hY in
omit [Smooth f.left] [GeometricallyIntegral (show X.carrier ⟶ Y.carrier from f.left)] in
theorem meets : CycleClass.Thom.IntersectionGeometry.MeetProperly Y p s a (ProperCycleLinearity.cyclePushforward f q s (Finsupp.single W 1)) := by
  rw [push_single f q s W B hB]
  intro A hA C hC
  have he : C = B := by
    by_contra hn
    have hz : ((f.left.residueDegree (CycleClass.Thom.IntersectionGeometry.supportPoint W.val) : ℚ) • Finsupp.single B (1 : ℚ)) C = 0 := by
      rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne hn, smul_zero]
    exact Finsupp.mem_support_iff.mp hC hz
  subst C
  exact hY A hA

include hd hB hX hY hgood in
theorem cycle : ProperCycleLinearity.cyclePushforward f (p + q) (p + s)
    (Supports.ProperCycle.intersectionBilinear X m p q (ProjectionFormula.Smooth.Cycle.flatMap f p a) (Finsupp.single W 1)) =
      Supports.ProperCycle.intersectionBilinear Y n p s a (ProperCycleLinearity.cyclePushforward f q s (Finsupp.single W 1)) := by
  let F := (ProperCycleLinearity.cyclePushforward f (p + q) (p + s)).comp
    (((Supports.ProperCycle.intersectionBilinear X m p q).flip (Finsupp.single W 1)).comp (ProjectionFormula.Smooth.Cycle.flatMap f p))
  let G := (Supports.ProperCycle.intersectionBilinear Y n p s).flip (ProperCycleLinearity.cyclePushforward f q s (Finsupp.single W 1))
  change F a = G a
  rw [CycleLinearExpansion.linear_sum F a, CycleLinearExpansion.linear_sum G a]
  apply Finset.sum_congr rfl
  intro A hA
  congr 1
  change ProperCycleLinearity.cyclePushforward f (p + q) (p + s)
    (Supports.ProperCycle.intersectionBilinear X m p q (ProjectionFormula.Smooth.Cycle.flatMap f p (Finsupp.single A 1)) (Finsupp.single W 1)) =
      Supports.ProperCycle.intersectionBilinear Y n p s (Finsupp.single A 1) (ProperCycleLinearity.cyclePushforward f q s (Finsupp.single W 1))
  rw [ProjectionFormula.Smooth.Cycle.flatMap, Finsupp.linearCombination_single, Integral.FiberCycles.cycle_single f m n,
    one_smul, push_single f q s W B hB, map_smul]
  simp only [Supports.ProperCycle.intersectionBilinear, Finsupp.linearCombination_single, one_smul]
  exact Pair.Projection.pair f m n p q s hd A W B hB
    (hX _ (flat_support f m n p a A hA) W (by simp)) (hY A hA) U (hgood A hA)

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Etale.Cycles
