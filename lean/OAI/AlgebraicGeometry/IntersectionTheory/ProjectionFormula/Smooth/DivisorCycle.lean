import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.ImageCodimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveFiberCycle

/-! # Divisor Cycle -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.DivisorCycle

noncomputable section

/-! Smooth inverse images of divisors have reduced codimension-one cycles
in every target dimension. Coefficients use the actual image generic points. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveFiberCycle

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver)
  (m n : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]

include n in
theorem generic_ne_supportPoint [IsIntegral Y.carrier] (B : Y.DimensionCycleSupport 1) :
    genericPoint Y.carrier ≠ CycleClass.Thom.IntersectionGeometry.supportPoint B.val := by
  intro he
  have hz : coheight (genericPoint Y.carrier) = 0 :=
    coheight_eq_zero.mpr (fun y _ => genericPoint_specializes y)
  rw [he, CurveSupports.coheight_one Y n B] at hz
  exact one_ne_zero hz

variable [Smooth f.left]

include m n

theorem fiber_codimension (B : Y.DimensionCycleSupport 1) (W : IrreducibleCloseds X.carrier)
    (hW : (W : Set X.carrier) ⊆ CurveFiberCycle.support f B) : 1 ≤ X.supportCodimension W := by
  by_contra hn
  have hzero : X.supportCodimension W = 0 := by omega
  have him := Flat.ImageCodimension.image_codimension_le f m n 0 ⟨W, hzero⟩
  change Y.supportCodimension (ProperCycleLinearity.imageSupport f W) ≤ 0 at him
  have hWB : ProperCycleLinearity.imageSupport f W ≤ B.val := by
    change (ProperCycleLinearity.imageSupport f W : Set Y.carrier) ⊆ B.val
    rw [ProperCycleLinearity.imageSupport_eq_image]
    rintro _ ⟨x, hx, rfl⟩
    exact hW hx
  have hh := (Supports.codimension_strictAnti Y n).antitone hWB
  rw [B.property] at hh
  omega

theorem point_mem_iff (A : X.DimensionCycleSupport 1) (B : Y.DimensionCycleSupport 1) :
    f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) ∈ (B.val : Set Y.carrier) ↔
      f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B.val := by
  constructor
  · intro h
    have hIB : ProperCycleLinearity.imageSupport f A.val ≤ B.val := by
      change closure {f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val)} ⊆ (B.val : Set Y.carrier)
      exact B.val.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr h)
    have he : ProperCycleLinearity.imageSupport f A.val = B.val := by
      by_contra hn
      have hh := Supports.codimension_strictAnti Y n (lt_of_le_of_ne hIB hn)
      rw [B.property] at hh
      have hb := Flat.ImageCodimension.image_codimension_le f m n 1 A
      omega
    exact (irreducibleSetEquivPoints.apply_symm_apply _).symm.trans (congrArg CycleClass.Thom.IntersectionGeometry.supportPoint he)
  · intro h
    rw [h]
    exact (B.val.isIrreducible.isGenericPoint_genericPoint B.val.isClosed).mem

theorem cycle_apply (B : Y.DimensionCycleSupport 1) (A : X.DimensionCycleSupport 1) :
    CurveFiberCycle.cycle f B A = if f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B.val then 1 else 0 := by
  rw [CurveFiberCycle.cycle, CycleClass.Thom.IntersectionGeometry.reducedClosedCycle_apply]
  congr 1
  apply propext
  have hp : CycleClass.Thom.IntersectionGeometry.supportPoint A.val ∈ CurveFiberCycle.support f B ↔ f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B.val :=
    point_mem_iff f m n A B
  constructor
  · rintro ⟨D, hD⟩
    apply hp.mp
    have hs := Supports.closedComponentSupport_subset X.carrier (CurveFiberCycle.support f B) D
    rw [hD] at hs
    exact hs ((A.val.isIrreducible.isGenericPoint_genericPoint A.val.isClosed).mem)
  · intro h
    exact Supports.support_eq_component X m 1 (CurveFiberCycle.support f B) (fiber_codimension f m n B)
      A ((Supports.supportPoint_mem_iff_subset (CurveFiberCycle.support f B) A.val).mp (hp.mpr h))

theorem flatMap_apply (a : Y.RationalDimensionCycle 1) (A : X.DimensionCycleSupport 1) :
    CurveFiberCycle.flatMap f a A = a.sum (fun B r => r * if f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B.val then 1 else 0) := by
  simp only [CurveFiberCycle.flatMap, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul, cycle_apply f m n]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.DivisorCycle
