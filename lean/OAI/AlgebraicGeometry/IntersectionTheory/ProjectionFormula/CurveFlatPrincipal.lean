import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveFiberCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.Integral

/-! # Curve Flat Principal -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveFlatPrincipal

noncomputable section

/-! Smooth pullback from an integral curve carries the actual principal
divisor to the principal divisor of its actual generic-field pullback. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveFiberCycle

theorem point_codimension (Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral Y.carrier]
    [SmoothOfRelativeDimension 1 Y.structureMap] (y : Y.carrier) (hy : y ≠ genericPoint Y.carrier) :
    Y.supportCodimension (irreducibleSetEquivPoints.symm y) = 1 := by
  let B := irreducibleSetEquivPoints.symm y
  have hb := CurveSupports.codimension_le Y 1 B
  by_contra hn
  have hzero : Y.supportCodimension B = 0 := by change Y.supportCodimension B ≠ 1 at hn; omega
  have ho := Open.Support.codimension_zero_isOpen Y 1 ⟨B, hzero⟩
  have ht : (B : Set Y.carrier) = Set.univ :=
    (show IsClopen (B : Set Y.carrier) from ⟨B.isClosed, ho⟩).eq_univ B.isIrreducible.nonempty
  have hg := B.isIrreducible.isGenericPoint_genericPoint B.isClosed
  change IsGenericPoint (CycleClass.Thom.IntersectionGeometry.supportPoint B) (B : Set Y.carrier) at hg
  rw [ht] at hg
  exact hy ((irreducibleSetEquivPoints.apply_symm_apply y).symm.trans (hg.eq (genericPoint_spec Y.carrier)))

theorem flatMap_apply_at_point {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    [SmoothOfRelativeDimension 1 Y.structureMap] (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
    (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (a : Y.RationalDimensionCycle 1) (A : X.DimensionCycleSupport 1) (B : Y.DimensionCycleSupport 1)
    (h : f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B.val) : CurveFiberCycle.flatMap f a A = a B := by
  rw [CurveFiberCycle.flatMap_apply f m]
  have he (D : Y.DimensionCycleSupport 1) : f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint D.val ↔ B = D := by
    rw [h]
    constructor
    · intro hd
      exact Subtype.ext (irreducibleSetEquivPoints.injective hd)
    · rintro rfl
      rfl
  simp only [he, Finsupp.sum, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  by_cases hb : B ∈ a.support
  · rw [ite_eq_left hb]
  · rw [ite_eq_right hb, Finsupp.notMem_support_iff.mp hb]

theorem flatMap_apply_at_generic {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral Y.carrier]
    [SmoothOfRelativeDimension 1 Y.structureMap] (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
    (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (a : Y.RationalDimensionCycle 1) (A : X.DimensionCycleSupport 1)
    (h : f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = genericPoint Y.carrier) : CurveFiberCycle.flatMap f a A = 0 := by
  rw [CurveFiberCycle.flatMap_apply f m]
  apply Finset.sum_eq_zero
  intro B _
  change a B * (if f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B.val then 1 else 0) = 0
  rw [h, ite_eq_right (CurveFiberCycle.generic_ne_supportPoint B), mul_zero]

theorem flatMap_principal {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral X.carrier]
    [IsIntegral Y.carrier] [SmoothOfRelativeDimension 1 Y.structureMap]
    (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
    (m : ℕ) [SmoothOfRelativeDimension m X.structureMap] (g : Y.carrier.functionField) :
    CurveFiberCycle.flatMap f (Principal.Integral.Cycle.cycle Y g) =
      Principal.Integral.Cycle.cycle X (ProjectionFormula.Smooth.GenericField.fieldMap (X := X.carrier) (Y := Y.carrier) f.left g) := by
  ext A
  rw [Principal.Integral.Cycle.cycle_apply]
  by_cases hy : f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = genericPoint Y.carrier
  · rw [flatMap_apply_at_generic f m _ A hy,
      ProjectionFormula.Smooth.GenericField.ord_generic_image (X := X.carrier) (Y := Y.carrier) f.left
        (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) (CurveSupports.coheight_one X m A) hy g, Int.cast_zero]
  · let B : Y.DimensionCycleSupport 1 :=
      ⟨irreducibleSetEquivPoints.symm (f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val)), point_codimension Y _ hy⟩
    have hb : CycleClass.Thom.IntersectionGeometry.supportPoint B.val = f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) :=
      irreducibleSetEquivPoints.apply_symm_apply _
    rw [flatMap_apply_at_point f m _ A B hb.symm, Principal.Integral.Cycle.cycle_apply, hb]
    apply congrArg (fun z : ℤ => (z : ℚ))
    exact (ProjectionFormula.Smooth.Order.ord_smooth (X := X.carrier) (Y := Y.carrier) f.left
      (ProjectionFormula.Smooth.GenericField.genericPoint_image (X := X.carrier) (Y := Y.carrier) f.left)
      (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) (CurveSupports.coheight_one X m A)
      (hb ▸ CurveSupports.coheight_one Y 1 B) g).symm

theorem flatMap_preserves_relations {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral X.carrier]
    [IsIntegral Y.carrier] [SmoothOfRelativeDimension 1 Y.structureMap]
    (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
    (m : ℕ) [SmoothOfRelativeDimension m X.structureMap] :
    CycleClass.Thom.IntersectionGeometry.rationalEquivalences Y 1 ≤ (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1).comap (CurveFiberCycle.flatMap f) := by
  apply Submodule.span_le.mpr
  intro d hd
  obtain ⟨g, hg, rfl⟩ := Principal.Integral.Cycle.principal_eq_cycle Y 1 d hd
  change CurveFiberCycle.flatMap f (Principal.Integral.Cycle.cycle Y g) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1
  rw [flatMap_principal f m]
  apply Submodule.subset_span
  apply Principal.Integral.Cycle.isPrincipal X m
  exact (map_ne_zero (ProjectionFormula.Smooth.GenericField.fieldMap (X := X.carrier) (Y := Y.carrier) f.left).hom).mpr hg

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveFlatPrincipal
