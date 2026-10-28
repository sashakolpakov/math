import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GeometricDivisorEuler
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorRestriction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.RelativeHeight

/-! # Intrinsic Divisor Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicDivisorEuler

noncomputable section

/-! The local principal-divisor intersection formula with native scheme
orders and the exact Tor multiplicities specified by ThomClass. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Intrinsic

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport

theorem order_restriction_eq_sum (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] [IsIntegral X.carrier]
    (A : X.DimensionCycleSupport 1) (C : X.DimensionCycleSupport 2)
    (hx : CycleClass.Thom.IntersectionGeometry.supportPoint C.val ∈ (A.val : Set X.carrier))
    (r : X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val))
    (hra : Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx r ≠ 0) :
    let R := X.carrier.presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val)
    let Y := CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val
    let y := CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx
    let f := algebraMap R X.carrier.functionField r
    let g := algebraMap (Y.presheaf.stalk y) Y.functionField
      (Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx r)
    ∃ S : Finset (Spec R),
      (∀ p ∈ S, p.asIdeal.height = 1 ∧ r ∈ p.asIdeal ∧
        X.supportCodimension (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) = 1) ∧
      (∀ p : Spec R, p.asIdeal.height = 1 → p ∉ S →
        X.carrier.ord f (X.carrier.fromSpecStalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) = 0) ∧
      (Y.ord g y : ℚ) = ∑ p ∈ S,
        (X.carrier.ord f (X.carrier.fromSpecStalk (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) : ℚ) *
          CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X (Stalk.DivisorSupport.primeClosure X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) p) A.val C.val := by
  obtain ⟨S, hS, hout, he⟩ := GeometricDivisorEuler.order_eq_intersection_sum X m A C hx r hra
  have hr : r ≠ 0 := by
    intro h
    apply hra
    rw [h, map_zero]
  have hleft := Affine.PrincipalOrder.stalk_order (CycleClass.Geometric.GenericPoint.reducedSupportScheme A.val)
    (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx)
    (Divisor.RelativeHeight.supportPreimage_coheight X m A C hx)
    (Local.Principal.supportStalkMap X.carrier A.val (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) hx r) hra
  refine ⟨S, hS, ?_, ?_⟩
  · intro p hp hpS
    rw [Stalk.DivisorRestriction.order_of_local_element X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) r hr p hp,
      hout p hp hpS]
    rfl
  · rw [hleft, Int.cast_natCast, he]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Stalk.DivisorRestriction.order_of_local_element X.carrier (CycleClass.Thom.IntersectionGeometry.supportPoint C.val) r hr p
      (hS p hp).1, Int.cast_natCast]

end Intrinsic

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicDivisorEuler
