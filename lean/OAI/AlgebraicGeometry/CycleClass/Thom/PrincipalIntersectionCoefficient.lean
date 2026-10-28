import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularOrder
import OAI.AlgebraicGeometry.CycleClass.Thom.Local.PrincipalIntersection
import OAI.AlgebraicGeometry.CycleClass.Thom.Relative.SupportCodimension

/-! # Principal Intersection Coefficient -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalIntersectionCoefficient.Constructions

noncomputable section

/-! The faithful principal-divisor coefficient is exactly the faithful
Serre--Tor intersection multiplicity when the first support has the
given principal stalk ideal and its restriction is the given rational germ. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.SupportStalkModule.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Local.PrincipalIntersection.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.RegularOrder.Constructions

set_option backward.isDefEq.respectTransparency false

theorem intersectionMultiplicity_eq_principalDivisorCoefficient
    (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (A B C : IrreducibleCloseds X.carrier)
    (hxA : IntersectionGeometry.supportPoint C ∈ (A : Set X.carrier))
    (hxB : IntersectionGeometry.supportPoint C ∈ (B : Set X.carrier))
    (hc : Order.coheight (IntersectionGeometry.supportPreimage B (IntersectionGeometry.supportPoint C) hxB) = 1)
    (r : X.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C))
    (hA : RingHom.ker (SupportStalkModule.Constructions.supportStalkMap X.carrier A (IntersectionGeometry.supportPoint C) hxA).hom = Ideal.span {r})
    (hBr : SupportStalkModule.Constructions.supportStalkMap X.carrier B (IntersectionGeometry.supportPoint C) hxB r ≠ 0)
    (g : (Geometric.GenericPoint.reducedSupportScheme B).functionField)
    (hg : g = algebraMap ((Geometric.GenericPoint.reducedSupportScheme B).presheaf.stalk
      (IntersectionGeometry.supportPreimage B (IntersectionGeometry.supportPoint C) hxB)) (Geometric.GenericPoint.reducedSupportScheme B).functionField
        (SupportStalkModule.Constructions.supportStalkMap X.carrier B (IntersectionGeometry.supportPoint C) hxB r)) :
    IntersectionGeometry.intersectionMultiplicity X A B C = IntersectionGeometry.principalDivisorCoefficient X B g C := by
  have hr : r ≠ 0 := fun h => hBr (by rw [h, map_zero])
  rw [Local.PrincipalIntersection.Constructions.intersectionMultiplicity_eq_order_left X A B C hxA hxB r hr hA hBr,
    IntersectionGeometry.principalDivisorCoefficient, dite_eq_left hxB, hg,
    Scheme.RegularOrder.Constructions.ord_algebraMap_stalk (Geometric.GenericPoint.reducedSupportScheme B) _ hc _ hBr, Int.cast_natCast]

theorem intersectionMultiplicity_eq_principalDivisorCoefficient_of_codimension
    (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (A B C : IrreducibleCloseds X.carrier)
    (hxA : IntersectionGeometry.supportPoint C ∈ (A : Set X.carrier))
    (hxB : IntersectionGeometry.supportPoint C ∈ (B : Set X.carrier))
    (hc : X.supportCodimension C = X.supportCodimension B + 1)
    (r : X.carrier.presheaf.stalk (IntersectionGeometry.supportPoint C))
    (hA : RingHom.ker (SupportStalkModule.Constructions.supportStalkMap X.carrier A (IntersectionGeometry.supportPoint C) hxA).hom = Ideal.span {r})
    (hBr : SupportStalkModule.Constructions.supportStalkMap X.carrier B (IntersectionGeometry.supportPoint C) hxB r ≠ 0)
    (g : (Geometric.GenericPoint.reducedSupportScheme B).functionField)
    (hg : g = algebraMap ((Geometric.GenericPoint.reducedSupportScheme B).presheaf.stalk
      (IntersectionGeometry.supportPreimage B (IntersectionGeometry.supportPoint C) hxB)) (Geometric.GenericPoint.reducedSupportScheme B).functionField
        (SupportStalkModule.Constructions.supportStalkMap X.carrier B (IntersectionGeometry.supportPoint C) hxB r)) :
    IntersectionGeometry.intersectionMultiplicity X A B C = IntersectionGeometry.principalDivisorCoefficient X B g C :=
  intersectionMultiplicity_eq_principalDivisorCoefficient X A B C hxA hxB
    (Relative.SupportCodimension.Constructions.supportPreimage_coheight_one X B C hxB hc) r hA hBr g hg

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PrincipalIntersectionCoefficient.Constructions
