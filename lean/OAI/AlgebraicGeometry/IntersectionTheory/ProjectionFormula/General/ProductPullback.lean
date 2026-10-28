import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Cycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DegreeCast
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductDivisorPullback

/-! # Product Pullback -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ProductPullback

noncomputable section

/-! The exterior product with the source fundamental cycle is exactly
smooth cycle pullback in every codimension through the second product projection. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ZeroComponents

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y)
  (m n p : ℕ) [SmoothOfRelativeDimension m X.structureMap]
  [SmoothOfRelativeDimension n Y.structureMap]

local instance product_dimension : SmoothOfRelativeDimension (m + n) P.space.structureMap :=
  ProductDimension.relativeDimension P m n

local instance : Smooth P.snd.left := ProductDivisorPullback.snd_smooth P

include m n

theorem product_contains (A : X.DimensionCycleSupport 0) (B : Y.DimensionCycleSupport p)
    (D : P.space.DimensionCycleSupport p) :
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
      exact (ProjectionFormula.Smooth.Cycle.point_mem_iff P.snd p (m + n) n D B).mp hh
  · rintro ⟨hA, hB⟩
    have hh : (D.val : Set P.space.carrier) ⊆ ProjectionFormula.Smooth.Cycle.support P.snd p B := by
      apply (Supports.supportPoint_mem_iff_subset (ProjectionFormula.Smooth.Cycle.support P.snd p B) D.val).mp
      change P.snd.left (CycleClass.Thom.IntersectionGeometry.supportPoint D.val) ∈ (B.val : Set Y.carrier)
      rw [hB]
      exact (B.val.isIrreducible.isGenericPoint_genericPoint B.val.isClosed).mem
    change (ProperCycleLinearity.imageSupport P.fst D.val : Set X.carrier) ⊆ A.val at hA
    rw [ProperCycleLinearity.imageSupport_eq_image] at hA
    intro x hx
    exact ⟨hA ⟨x, hx, rfl⟩, hh hx⟩

theorem product_cycle_apply (A : X.DimensionCycleSupport 0) (B : Y.DimensionCycleSupport p)
    (D : P.space.DimensionCycleSupport p) :
    CycleClass.Thom.IntersectionGeometry.reducedClosedCycle P.space p (CycleClass.Thom.IntersectionGeometry.productClosedSupport X Y P.space P.fst P.snd A.val B.val) D =
      if A = ZeroComponents.containingComponent X m (ProperCycleLinearity.imageSupport P.fst D.val) ∧
        P.snd.left (CycleClass.Thom.IntersectionGeometry.supportPoint D.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B.val then 1 else 0 := by
  rw [CycleClass.Thom.IntersectionGeometry.reducedClosedCycle_apply]
  congr 1
  apply propext
  rw [← product_contains P m n p A B D]
  constructor
  · rintro ⟨C, hC⟩
    rw [← hC]
    exact Supports.closedComponentSupport_subset _ _ C
  · intro hD
    apply Supports.support_eq_component P.space (m + n) p _ _ D hD
    intro W hW
    exact ProjectionFormula.Smooth.Cycle.fiber_codimension P.snd p (m + n) n B W (fun x hx => (hW hx).2)

theorem secondPullback_eq_flatMap (a : Y.RationalDimensionCycle p) :
    P.secondPullbackCycle p a = ProjectionFormula.Smooth.Cycle.flatMap P.snd p a := by
  ext D
  have hcycle (A : X.DimensionCycleSupport 0) (B : Y.DimensionCycleSupport p) :
      CycleClass.Thom.IntersectionGeometry.reducedClosedCycle P.space (0 + p)
          (CycleClass.Thom.IntersectionGeometry.productClosedSupport X Y P.space P.fst P.snd A.val B.val)
          ⟨D.val, D.property.trans (Nat.zero_add p).symm⟩ =
        CycleClass.Thom.IntersectionGeometry.reducedClosedCycle P.space p
          (CycleClass.Thom.IntersectionGeometry.productClosedSupport X Y P.space P.fst P.snd A.val B.val) D := by
    rw [CycleClass.Thom.IntersectionGeometry.reducedClosedCycle_apply, CycleClass.Thom.IntersectionGeometry.reducedClosedCycle_apply]
  rw [← DegreeCast.ExteriorCycleLinear.secondPullbackMap_apply,
    DegreeCast.ExteriorCycleLinear.secondPullbackMap, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, DegreeCast.cycle_apply]
  simp only [DegreeCast.ExteriorCycleLinear.exteriorMap, Finsupp.linearCombination_apply, Finsupp.sum,
    LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.finsetSum_apply, Finsupp.smul_apply,
    smul_eq_mul, hcycle, product_cycle_apply P m n p, ZeroComponents.fundamentalCycle_apply X m, one_mul]
  rw [ProjectionFormula.Smooth.Cycle.flatMap_apply P.snd p (m + n) n]
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

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ProductPullback
