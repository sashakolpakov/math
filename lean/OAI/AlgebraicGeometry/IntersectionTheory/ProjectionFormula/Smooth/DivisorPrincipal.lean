import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.DivisorCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.Fundamental
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.Integral

/-! # Divisor Principal -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.DivisorPrincipal

noncomputable section

/-! Smooth pullback between integral smooth presentations in arbitrary dimensions carries the actual principal
divisor to the principal divisor of its actual generic-field pullback. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CurveFiberCycle

theorem image_codimension {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral Y.carrier]
    (f : X.toOver ⟶ Y.toOver) [Smooth f.left] (m n : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]
    (A : X.DimensionCycleSupport 1)
    (hy : f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) ≠ genericPoint Y.carrier) :
    Y.supportCodimension (ProperCycleLinearity.imageSupport f A.val) = 1 := by
  have h := Flat.ImageCodimension.image_codimension_le f m n 1 A
  by_contra hn
  have hz : Y.supportCodimension (ProperCycleLinearity.imageSupport f A.val) = 0 := by omega
  have he := Integral.Fundamental.support_unique Y n ⟨ProperCycleLinearity.imageSupport f A.val, hz⟩
  have hp := congrArg (fun C : Y.DimensionCycleSupport 0 => CycleClass.Thom.IntersectionGeometry.supportPoint C.val) he
  exact hy ((irreducibleSetEquivPoints.apply_symm_apply _).symm.trans
    (hp.trans (Integral.Fundamental.whole_point Y)))

theorem flatMap_apply_at_point {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation}
    (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
    (m n : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    [SmoothOfRelativeDimension n Y.structureMap]
    (a : Y.RationalDimensionCycle 1) (A : X.DimensionCycleSupport 1) (B : Y.DimensionCycleSupport 1)
    (h : f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B.val) : CurveFiberCycle.flatMap f a A = a B := by
  rw [DivisorCycle.flatMap_apply f m n]
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
    (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
    (m n : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    [SmoothOfRelativeDimension n Y.structureMap]
    (a : Y.RationalDimensionCycle 1) (A : X.DimensionCycleSupport 1)
    (h : f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = genericPoint Y.carrier) : CurveFiberCycle.flatMap f a A = 0 := by
  rw [DivisorCycle.flatMap_apply f m n]
  apply Finset.sum_eq_zero
  intro B _
  change a B * (if f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = CycleClass.Thom.IntersectionGeometry.supportPoint B.val then 1 else 0) = 0
  rw [h, ite_eq_right (DivisorCycle.generic_ne_supportPoint n B), mul_zero]

theorem flatMap_principal {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral X.carrier]
    [IsIntegral Y.carrier]
    (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
    (m n : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    [SmoothOfRelativeDimension n Y.structureMap] (g : Y.carrier.functionField) :
    CurveFiberCycle.flatMap f (Principal.Integral.Cycle.cycle Y g) =
      Principal.Integral.Cycle.cycle X (GenericField.fieldMap (X := X.carrier) (Y := Y.carrier) f.left g) := by
  ext A
  rw [Principal.Integral.Cycle.cycle_apply]
  by_cases hy : f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) = genericPoint Y.carrier
  · rw [flatMap_apply_at_generic f m n _ A hy,
      GenericField.ord_generic_image (X := X.carrier) (Y := Y.carrier) f.left
        (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) (CurveSupports.coheight_one X m A) hy g, Int.cast_zero]
  · let B : Y.DimensionCycleSupport 1 :=
      ⟨irreducibleSetEquivPoints.symm (f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val)), image_codimension f m n A hy⟩
    have hb : CycleClass.Thom.IntersectionGeometry.supportPoint B.val = f.left (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) :=
      irreducibleSetEquivPoints.apply_symm_apply _
    rw [flatMap_apply_at_point f m n _ A B hb.symm, Principal.Integral.Cycle.cycle_apply, hb]
    apply congrArg (fun z : ℤ => (z : ℚ))
    exact (Order.ord_smooth (X := X.carrier) (Y := Y.carrier) f.left
      (GenericField.genericPoint_image (X := X.carrier) (Y := Y.carrier) f.left)
      (CycleClass.Thom.IntersectionGeometry.supportPoint A.val) (CurveSupports.coheight_one X m A)
      (hb ▸ CurveSupports.coheight_one Y n B) g).symm

theorem flatMap_preserves_relations {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral X.carrier]
    [IsIntegral Y.carrier]
    (f : X.toOver ⟶ Y.toOver) [Smooth f.left]
    (m n : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    [SmoothOfRelativeDimension n Y.structureMap] :
    CycleClass.Thom.IntersectionGeometry.rationalEquivalences Y 1 ≤ (CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1).comap (CurveFiberCycle.flatMap f) := by
  apply Submodule.span_le.mpr
  intro d hd
  obtain ⟨g, hg, rfl⟩ := Principal.Integral.Cycle.principal_eq_cycle Y n d hd
  change CurveFiberCycle.flatMap f (Principal.Integral.Cycle.cycle Y g) ∈ CycleClass.Thom.IntersectionGeometry.rationalEquivalences X 1
  rw [flatMap_principal f m n]
  apply Submodule.subset_span
  apply Principal.Integral.Cycle.isPrincipal X m
  exact (map_ne_zero (GenericField.fieldMap (X := X.carrier) (Y := Y.carrier) f.left).hom).mpr hg

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.DivisorPrincipal
