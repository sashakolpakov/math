import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveFlatComponents
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DegreeCast
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductDimension

/-! # Product Divisor Pullback -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductDivisorPullback

noncomputable section

/-! The exterior product with the source fundamental cycle is exactly
smooth divisor pullback through the second product projection. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ZeroComponents

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y)
  (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]
  [SmoothOfRelativeDimension 1 Y.structureMap]

local instance product_dimension : SmoothOfRelativeDimension (m + 1) P.space.structureMap :=
  ProductDimension.relativeDimension P m 1

omit [SmoothOfRelativeDimension 1 Y.structureMap] in
theorem snd_smooth : Smooth P.snd.left := by
  exact MorphismProperty.of_isPullback
    (Over.isPullback_of_binaryFan_isLimit (Limits.BinaryFan.mk P.fst P.snd) P.isLimit)
    (inferInstance : Smooth X.structureMap)

local instance : Smooth P.snd.left := snd_smooth P

include m

theorem product_contains (A : X.DimensionCycleSupport 0) (B : Y.DimensionCycleSupport 1)
    (D : P.space.DimensionCycleSupport 1) :
    (D.val : Set P.space.carrier) ⊆ CycleClass.Thom.IntersectionGeometry.productClosedSupport X Y P.space P.fst P.snd A.val B.val ↔
      A = ZeroComponents.containingComponent X m (ProperCycleLinearity.imageSupport P.fst D.val) ∧
      P.snd.left (CycleClass.Thom.IntersectionGeometry.supportPoint D.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B.val := by
  rw [← ZeroComponents.subset_zero_iff X m]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · change (ProperCycleLinearity.imageSupport P.fst D.val : Set X.carrier) ⊆ A.val
      rw [ProperCycleLinearity.imageSupport_eq_image]
      rintro _ ⟨x, hx, rfl⟩
      exact (h hx).1
    · have hh := (h ((D.val.isIrreducible.isGenericPoint_genericPoint D.val.isClosed).mem)).2
      change P.snd.left (CycleClass.Thom.IntersectionGeometry.supportPoint D.val) ∈ (B.val : Set Y.carrier) at hh
      rwa [CurveSupports.support_eq_singleton, Set.mem_singleton_iff] at hh
  · rintro ⟨hA, hB⟩
    have hh : (D.val : Set P.space.carrier) ⊆ CurveFiberCycle.support P.snd B := by
      apply (Supports.supportPoint_mem_iff_subset (CurveFiberCycle.support P.snd B) D.val).mp
      change P.snd.left (CycleClass.Thom.IntersectionGeometry.supportPoint D.val) ∈ (B.val : Set Y.carrier)
      rw [CurveSupports.support_eq_singleton, Set.mem_singleton_iff]
      exact hB
    change (ProperCycleLinearity.imageSupport P.fst D.val : Set X.carrier) ⊆ A.val at hA
    rw [ProperCycleLinearity.imageSupport_eq_image] at hA
    intro x hx
    exact ⟨hA ⟨x, hx, rfl⟩, hh hx⟩

theorem product_cycle_apply (A : X.DimensionCycleSupport 0) (B : Y.DimensionCycleSupport 1)
    (D : P.space.DimensionCycleSupport 1) :
    CycleClass.Thom.IntersectionGeometry.reducedClosedCycle P.space 1 (CycleClass.Thom.IntersectionGeometry.productClosedSupport X Y P.space P.fst P.snd A.val B.val) D =
      if A = ZeroComponents.containingComponent X m (ProperCycleLinearity.imageSupport P.fst D.val) ∧
        P.snd.left (CycleClass.Thom.IntersectionGeometry.supportPoint D.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B.val then 1 else 0 := by
  rw [CycleClass.Thom.IntersectionGeometry.reducedClosedCycle_apply]
  congr 1
  apply propext
  rw [← product_contains P m A B D]
  constructor
  · rintro ⟨C, hC⟩
    rw [← hC]
    exact Supports.closedComponentSupport_subset _ _ C
  · intro hD
    apply Supports.support_eq_component P.space (m + 1) 1 _ _ D hD
    intro W hW
    exact CurveFiberCycle.fiber_codimension P.snd (m + 1) B W (fun x hx => (hW hx).2)

theorem secondPullback_eq_flatMap (a : Y.RationalDimensionCycle 1) :
    P.secondPullbackCycle 1 a = CurveFiberCycle.flatMap P.snd a := by
  ext D
  change CycleClass.Thom.IntersectionGeometry.exteriorCycleProduct X Y P.space P.fst P.snd P.isLimit 0 1 (ProperCycleLinearity.fundamentalCycle X) a D = _
  rw [← DegreeCast.ExteriorCycleLinear.exteriorMap_apply X Y P.space P.fst P.snd P.isLimit 0 1]
  simp only [DegreeCast.ExteriorCycleLinear.exteriorMap, Finsupp.linearCombination_apply, Finsupp.sum,
    LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, product_cycle_apply P m, ZeroComponents.fundamentalCycle_apply X m, one_mul]
  rw [CurveFiberCycle.flatMap_apply P.snd (m + 1)]
  let A := ZeroComponents.containingComponent X m (ProperCycleLinearity.imageSupport P.fst D.val)
  rw [Finset.sum_eq_single A]
  · simp only [A, true_and, Finsupp.sum]
  · intro A' _ hA
    apply Finset.sum_eq_zero
    intro B _
    simp [show A' ≠ ZeroComponents.containingComponent X m (ProperCycleLinearity.imageSupport P.fst D.val) from hA]
  · intro hA
    have ha : A ∈ (ProperCycleLinearity.fundamentalCycle X).support :=
      Finsupp.mem_support_iff.mpr (by rw [ZeroComponents.fundamentalCycle_apply X m]; norm_num)
    exact (hA ha).elim

theorem secondPullback_preserves_relations :
    CycleClass.Thom.IntersectionGeometry.rationalEquivalences Y 1 ≤
      (CycleClass.Thom.IntersectionGeometry.rationalEquivalences P.space 1).comap (DegreeCast.ExteriorCycleLinear.secondPullbackMap P 1) := by
  intro a ha
  change DegreeCast.ExteriorCycleLinear.secondPullbackMap P 1 a ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences P.space 1
  rw [DegreeCast.ExteriorCycleLinear.secondPullbackMap_apply, secondPullback_eq_flatMap P m]
  exact CurveFlatComponents.flatMap_preserves_relations P.snd (m + 1) ha

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductDivisorPullback
