import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Closed.PrincipalCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.DivisorImage

/-! # Nested Cycle Relation -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedCycleRelation

noncomputable section

section

/-! Principal cycles on curve supports inside a surface give native
ambient zero-cycle relations, with explicit coefficients at surface points. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

namespace Principal

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.ClosedSectionCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CyclePushforward OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.DivisorNorm

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ) (W : IrreducibleCloseds X.carrier)
  (Z : IrreducibleCloseds (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField)

def cycle : X.RationalDimensionCycle p :=
  CyclePushforward.degreeComponent X p (CyclePushforward.pointPushforward (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W)
    (Affine.DivisorNorm.rationalPrincipalDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) g))

theorem coefficient (C : X.DimensionCycleSupport p)
    (hxW : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (W : Set X.carrier)) :
    cycle X p W Z g C =
      if hxZ : CycleClass.Thom.IntersectionGeometry.supportPreimage W (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW ∈ (Z : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) then
        ((CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).ord g
          (CycleClass.Thom.IntersectionGeometry.supportPreimage Z (CycleClass.Thom.IntersectionGeometry.supportPreimage W (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW) hxZ) : ℚ)
      else 0 := by
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hxW
  rw [cycle, Principal.ClosedSectionCycle.degreeComponent_apply, CyclePushforward.pointPushforward_comp]
  change CyclePushforward.pointPushforward (CycleClass.Geometric.GenericPoint.reducedSupportι W)
    (CyclePushforward.pointPushforward (CycleClass.Geometric.GenericPoint.reducedSupportι Z) (Affine.DivisorNorm.rationalPrincipalDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z) g))
      (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) = _
  rw [PushforwardFiber.pointPushforward_uniqueFiber (CycleClass.Geometric.GenericPoint.reducedSupportι W) y (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
    (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W _ hxW)
    (fun z hz => (CycleClass.Geometric.GenericPoint.reducedSupportι W).isEmbedding.injective (hz.trans (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec W _ hxW).symm)),
    Principal.ClosedSectionCycle.residueDegree_immersion, Nat.cast_one, mul_one]
  by_cases hy : y ∈ (Z : Set (CycleClass.Geometric.GenericPoint.reducedSupportScheme W))
  · rw [dite_eq_left hy]
    rw [PushforwardFiber.pointPushforward_uniqueFiber (CycleClass.Geometric.GenericPoint.reducedSupportι Z) (CycleClass.Thom.IntersectionGeometry.supportPreimage Z y hy) y
      (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec Z y hy)
      (fun z hz => (CycleClass.Geometric.GenericPoint.reducedSupportι Z).isEmbedding.injective (hz.trans (CycleClass.Thom.IntersectionGeometry.supportPreimage_spec Z y hy).symm)),
      Principal.ClosedSectionCycle.residueDegree_immersion, Nat.cast_one, mul_one, Affine.DivisorNorm.rationalPrincipalDivisor_apply]
  · rw [dite_eq_right hy]
    apply PushforwardFiber.pointPushforward_apply_eq_zero
    intro z _ hz
    apply hy
    rw [← hz, ← CycleClass.Geometric.GenericPoint.range_reducedSupportι]
    exact ⟨z, rfl⟩

theorem coefficient_zero (C : X.DimensionCycleSupport p)
    (hxW : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∉ (W : Set X.carrier)) : cycle X p W Z g C = 0 := by
  rw [cycle, Principal.ClosedSectionCycle.degreeComponent_apply]
  apply PushforwardFiber.pointPushforward_apply_eq_zero
  intro z _ hz
  apply hxW
  rw [← hz, ← CycleClass.Geometric.GenericPoint.range_reducedSupportι]
  exact ⟨CycleClass.Geometric.GenericPoint.reducedSupportι Z z, rfl⟩

omit p W Z g in
theorem isPrincipal (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (W : X.DimensionCycleSupport 1) (Z : IrreducibleCloseds (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val))
    (hZ : Order.coheight (CycleClass.Thom.IntersectionGeometry.supportPoint Z) = 1) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField)
    (hg : g ≠ 0) : CycleClass.Thom.IntersectionGeometry.IsPrincipalDivisor X 3 (cycle X 3 W.val Z g) := by
  apply Closed.PrincipalCycle.isPrincipal X (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W.val) 3 _ g hg
  have h := Support.DivisorImage.codimension X W.val m Z hZ
  change X.supportCodimension (Support.DivisorImage.image X W.val Z) + 1 = 3
  rw [h, W.property]

end Principal

end

/-! A principal divisor on a divisor inside an arbitrary support is
an actual ambient rational-equivalence generator in the correct degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem isPrincipal (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m r p : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (W : X.DimensionCycleSupport r) (Z : IrreducibleCloseds (CycleClass.Geometric.GenericPoint.reducedSupportScheme W.val))
    (hZ : Order.coheight (CycleClass.Thom.IntersectionGeometry.supportPoint Z) = 1) (hp : p = r + 2)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z).functionField) (hg : g ≠ 0) :
    CycleClass.Thom.IntersectionGeometry.IsPrincipalDivisor X p (Principal.cycle X p W.val Z g) := by
  apply Closed.PrincipalCycle.isPrincipal X (CycleClass.Geometric.GenericPoint.reducedSupportι Z ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W.val) p _ g hg
  have h := Support.DivisorImage.codimension X W.val m Z hZ
  change X.supportCodimension (Support.DivisorImage.image X W.val Z) + 1 = p
  rw [h, W.property, hp]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedCycleRelation
