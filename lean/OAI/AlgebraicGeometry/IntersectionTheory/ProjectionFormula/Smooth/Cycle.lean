import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Flat.ImageCodimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports

/-! # Cycle -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Cycle

noncomputable section

/-! Reduced inverse-image cycles in every codimension. A coefficient is one
precisely when its generic point maps to the specified target generic point. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (f : X.toOver ⟶ Y.toOver) (p : ℕ)

def support (B : Y.DimensionCycleSupport p) : Closeds X.carrier :=
  ⟨f.left ⁻¹' (B.val : Set Y.carrier), B.val.isClosed.preimage f.left.continuous⟩

def cycle (B : Y.DimensionCycleSupport p) : X.RationalDimensionCycle p :=
  CycleClass.Thom.IntersectionGeometry.reducedClosedCycle X p (support f p B)

def flatMap : Y.RationalDimensionCycle p →ₗ[ℚ] X.RationalDimensionCycle p :=
  Finsupp.linearCombination ℚ (cycle f p)

variable (m n : ℕ) [SmoothOfRelativeDimension m X.structureMap]
  [SmoothOfRelativeDimension n Y.structureMap] [Smooth f.left]

include m n

theorem fiber_codimension (B : Y.DimensionCycleSupport p) (W : IrreducibleCloseds X.carrier)
    (hW : (W : Set X.carrier) ⊆ support f p B) : p ≤ X.supportCodimension W := by
  have him := Flat.ImageCodimension.image_codimension_le f m n
    (X.supportCodimension W) ⟨W, rfl⟩
  have hWB : ProperCycleLinearity.imageSupport f W ≤ B.val := by
    change (ProperCycleLinearity.imageSupport f W : Set Y.carrier) ⊆ B.val
    rw [ProperCycleLinearity.imageSupport_eq_image]
    rintro _ ⟨x, hx, rfl⟩
    exact hW hx
  have hh := (Supports.codimension_strictAnti Y n).antitone hWB
  rw [B.property] at hh
  exact hh.trans him

theorem point_mem_iff (A : X.DimensionCycleSupport p) (B : Y.DimensionCycleSupport p) :
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
      have hb := Flat.ImageCodimension.image_codimension_le f m n p A
      omega
    exact (irreducibleSetEquivPoints.apply_symm_apply _).symm.trans (congrArg CycleClass.Thom.IntersectionGeometry.supportPoint he)
  · intro h
    rw [h]
    exact (B.val.isIrreducible.isGenericPoint_genericPoint B.val.isClosed).mem

theorem cycle_apply (B : Y.DimensionCycleSupport p) (A : X.DimensionCycleSupport p) :
    cycle f p B A = if f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B.val then 1 else 0 := by
  rw [cycle, CycleClass.Thom.IntersectionGeometry.reducedClosedCycle_apply]
  congr 1
  apply propext
  have hp : CycleClass.Thom.IntersectionGeometry.supportPoint A.val ∈ support f p B ↔
      f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B.val := point_mem_iff f p m n A B
  constructor
  · rintro ⟨D, hD⟩
    apply hp.mp
    have hs := Supports.closedComponentSupport_subset X.carrier (support f p B) D
    rw [hD] at hs
    exact hs ((A.val.isIrreducible.isGenericPoint_genericPoint A.val.isClosed).mem)
  · intro h
    exact Supports.support_eq_component X m p (support f p B)
      (fiber_codimension f p m n B) A
      ((Supports.supportPoint_mem_iff_subset (support f p B) A.val).mp (hp.mpr h))

theorem flatMap_apply (a : Y.RationalDimensionCycle p) (A : X.DimensionCycleSupport p) :
    flatMap f p a A = a.sum
      (fun B r => r * if f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B.val then 1 else 0) := by
  simp only [flatMap, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul, cycle_apply f p m n]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.Cycle
