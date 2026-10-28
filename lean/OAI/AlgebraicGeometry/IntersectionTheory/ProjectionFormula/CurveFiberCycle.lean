import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.ComponentFactor
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveSupports

/-! # Curve Fiber Cycle -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveFiberCycle

noncomputable section

/-! Smooth inverse images of curve points have their actual reduced
codimension-one cycle, with coefficient one on each fiber component. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order
open scoped Classical

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)

def support (B : Y.DimensionCycleSupport 1) : Closeds X.carrier :=
  ⟨f.left ⁻¹' (B.val : Set Y.carrier), B.val.isClosed.preimage f.left.continuous⟩

def cycle (B : Y.DimensionCycleSupport 1) : X.RationalDimensionCycle 1 :=
  CycleClass.Thom.IntersectionGeometry.reducedClosedCycle X 1 (support f B)

def flatMap : Y.RationalDimensionCycle 1 →ₗ[ℚ] X.RationalDimensionCycle 1 :=
  Finsupp.linearCombination ℚ (cycle f)

theorem generic_ne_supportPoint [IsIntegral Y.carrier] [SmoothOfRelativeDimension 1 Y.structureMap]
    (B : Y.DimensionCycleSupport 1) : genericPoint Y.carrier ≠ CycleClass.Thom.IntersectionGeometry.supportPoint B.val := by
  intro he
  have hz : coheight (genericPoint Y.carrier) = 0 :=
    coheight_eq_zero.mpr (fun y _ => genericPoint_specializes y)
  rw [he, CurveSupports.coheight_one Y 1 B] at hz
  exact one_ne_zero hz

theorem fiber_codimension [SmoothOfRelativeDimension 1 Y.structureMap]
    [Smooth f.left] (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (B : Y.DimensionCycleSupport 1) (W : IrreducibleCloseds X.carrier)
    (hW : (W : Set X.carrier) ⊆ support f B) : 1 ≤ X.supportCodimension W := by
  by_contra hn
  have hzero : X.supportCodimension W = 0 := by omega
  let : IsOpenImmersion (CycleClass.Geometric.GenericPoint.reducedSupportι W) := Open.Support.inclusion_isOpenImmersion W
    (Open.Support.codimension_zero_isOpen X m ⟨W, hzero⟩)
  have he := Integral.ComponentFactor.generic_coheight Y (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ f.left)
  change coheight (f.left (CycleClass.Geometric.GenericPoint.reducedSupportι W (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)))) = 0 at he
  rw [CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq] at he
  change coheight (f.left (CycleClass.Thom.IntersectionGeometry.supportPoint W)) = 0 at he
  have hx := hW ((W.isIrreducible.isGenericPoint_genericPoint W.isClosed).mem)
  change f.left (CycleClass.Thom.IntersectionGeometry.supportPoint W) ∈ (B.val : Set Y.carrier) at hx
  rw [CurveSupports.support_eq_singleton Y B, Set.mem_singleton_iff] at hx
  rw [hx, CurveSupports.coheight_one Y 1 B] at he
  exact one_ne_zero he

theorem cycle_apply [SmoothOfRelativeDimension 1 Y.structureMap]
    [Smooth f.left] (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (B : Y.DimensionCycleSupport 1) (A : X.DimensionCycleSupport 1) :
    cycle f B A = if f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B.val then 1 else 0 := by
  rw [cycle, CycleClass.Thom.IntersectionGeometry.reducedClosedCycle_apply]
  congr 1
  apply propext
  have hp : CycleClass.Thom.IntersectionGeometry.supportPoint A.val ∈ support f B ↔ f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B.val := by
    change f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) ∈ (B.val : Set Y.carrier) ↔ _
    rw [CurveSupports.support_eq_singleton, Set.mem_singleton_iff]
  constructor
  · rintro ⟨D, hD⟩
    apply hp.mp
    have hs := Supports.closedComponentSupport_subset X.carrier (support f B) D
    rw [hD] at hs
    exact hs ((A.val.isIrreducible.isGenericPoint_genericPoint A.val.isClosed).mem)
  · intro h
    exact Supports.support_eq_component X m 1 (support f B) (fiber_codimension f m B)
      A ((Supports.supportPoint_mem_iff_subset (support f B) A.val).mp (hp.mpr h))

theorem flatMap_apply [SmoothOfRelativeDimension 1 Y.structureMap]
    [Smooth f.left] (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (a : Y.RationalDimensionCycle 1) (A : X.DimensionCycleSupport 1) :
    flatMap f a A = a.sum (fun B r => r * if f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B.val then 1 else 0) := by
  simp only [flatMap, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul, cycle_apply f m]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveFiberCycle
