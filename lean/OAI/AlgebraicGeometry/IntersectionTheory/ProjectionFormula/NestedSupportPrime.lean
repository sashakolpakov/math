import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupportStalk
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.StalkImage
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.RelativeHeight
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.OrderQuotientTransport

/-! # Nested Support Prime -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupportPrime

noncomputable section

/-! A curve inside a surface support gives the actual height-one prime
of the surface stalk, and quotient orders are the native curve-stalk orders. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupport OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupportStalk

theorem height (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap]
    (W : X.DimensionCycleSupport 1) (A : X.DimensionCycleSupport 2) (hAW : A.val ≤ W.val)
    (x : X.carrier) (hxA : x ∈ (A.val : Set X.carrier)) (hxW : x ∈ (W.val : Set X.carrier)) :
    (RingHom.ker (NestedSupportStalk.stalkMap X.carrier A.val W.val hAW x hxA hxW).hom).height = 1 := by
  change (Integral.StalkImage.prime (NestedSupport.inclusion X.carrier A.val W.val hAW)
    (CycleClass.Thom.IntersectionGeometry.supportPreimage A.val x hxA) (CycleClass.Thom.IntersectionGeometry.supportPreimage W.val x hxW)
    (NestedSupport.inclusion_preimage X.carrier A.val W.val hAW x hxA hxW)).asIdeal.height = 1
  rw [Integral.StalkImage.height, NestedSupport.inclusion_genericPoint]
  exact Divisor.RelativeHeight.supportPreimage_coheight X m W A _

theorem order (X : Scheme) (A W : IrreducibleCloseds X) (hAW : A ≤ W)
    (x : X) (hxA : x ∈ (A : Set X)) (hxW : x ∈ (W : Set X))
    (r : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W x hxW)) :
    Ring.ord ((CycleClass.Geometric.GenericPoint.reducedSupportScheme A).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage A x hxA))
        (NestedSupportStalk.stalkMap X A W hAW x hxA hxW r) =
      Ring.ord (((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk (CycleClass.Thom.IntersectionGeometry.supportPreimage W x hxW)) ⧸
          RingHom.ker (NestedSupportStalk.stalkMap X A W hAW x hxA hxW).hom)
        (Ideal.Quotient.mk _ r) :=
  OrderQuotientTransport.ord (NestedSupportStalk.stalkMap X A W hAW x hxA hxW).hom
    (NestedSupportStalk.surjective X A W hAW x hxA hxW) r

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NestedSupportPrime
