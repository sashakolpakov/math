import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeOrder
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CanonicalSurfaceReciprocity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicDivisorRatio

/-! # Prime Ratio Order -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeRatioOrder

noncomputable section

/-! The numerator-minus-denominator terms of local reciprocity are
actual geometric orders on the ambient surface and its curve supports. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorSupport OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CanonicalSurfaceReciprocity

variable (X : Scheme) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
  (x : X) (p : PrimeSpectrum (X.presheaf.stalk x))

theorem ambient (hp : p.asIdeal.height = 1) (a b : X.presheaf.stalk x)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    (X.ord (algebraMap (X.presheaf.stalk x) X.functionField a /
      algebraMap (X.presheaf.stalk x) X.functionField b) (X.fromSpecStalk x p) : ℚ) =
        CanonicalSurfaceReciprocity.weight (X.presheaf.stalk x) p a - CanonicalSurfaceReciprocity.weight (X.presheaf.stalk x) p b := by
  have haK := (map_ne_zero_iff _ (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)).mpr ha
  have hbK := (map_ne_zero_iff _ (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)).mpr hb
  rw [IntrinsicDivisorRatio.Intrinsic.ord_div X _ _ haK hbK, Int.cast_sub,
    DivisorRestriction.order_of_local_element X x a ha p hp,
    DivisorRestriction.order_of_local_element X x b hb p hp, Int.cast_natCast, Int.cast_natCast]
  rfl

theorem support (hx : Order.coheight x = 2) (hp : p.asIdeal.height = 1)
    (a b : X.presheaf.stalk x) (ha : a ∉ p.asIdeal) (hb : b ∉ p.asIdeal) :
    let W := DivisorSupport.primeClosure X x p
    let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W x (DivisorSupport.point_mem_primeClosure X x p)
    let σ := Local.Principal.supportStalkMap X W x (DivisorSupport.point_mem_primeClosure X x p)
    ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).ord
      (algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk y) (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField (σ a) /
        algebraMap ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).presheaf.stalk y) (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField (σ b)) y : ℚ) =
      CanonicalSurfaceReciprocity.restrictedOrder (X.presheaf.stalk x) p a - CanonicalSurfaceReciprocity.restrictedOrder (X.presheaf.stalk x) p b := by
  let W := DivisorSupport.primeClosure X x p
  let Y := CycleClass.Geometric.GenericPoint.reducedSupportScheme W
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W x (DivisorSupport.point_mem_primeClosure X x p)
  let σ := Local.Principal.supportStalkMap X W x (DivisorSupport.point_mem_primeClosure X x p)
  have haσ := PrimeOrder.image_ne_zero X x p a ha
  have hbσ := PrimeOrder.image_ne_zero X x p b hb
  have haK : algebraMap (Y.presheaf.stalk y) Y.functionField (σ a) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField)).mpr haσ
  have hbK : algebraMap (Y.presheaf.stalk y) Y.functionField (σ b) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField)).mpr hbσ
  change (Y.ord (_ / _) y : ℚ) = _
  rw [IntrinsicDivisorRatio.Intrinsic.ord_div Y _ _ haK hbK, Int.cast_sub]
  have hea := PrimeOrder.geometric_order X x p hx hp a ha
  have heb := PrimeOrder.geometric_order X x p hx hp b hb
  change Y.ord (algebraMap (Y.presheaf.stalk y) Y.functionField (σ a)) y = _ at hea
  change Y.ord (algebraMap (Y.presheaf.stalk y) Y.functionField (σ b)) y = _ at heb
  rw [hea, heb, Int.cast_natCast, Int.cast_natCast]
  rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeRatioOrder
