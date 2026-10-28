import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AdjacentSupportCoheight
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CanonicalSurfaceReciprocity
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.OrderQuotientTransport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntrinsicDivisorRatio

/-! # Stalk Ratio Order -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.StalkRatioOrder

noncomputable section

/-! Native geometric ratio orders on an arbitrary integral support
equal the numerator-minus-denominator orders in its actual kernel quotient. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.Principal OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.PrimeQuotient OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CanonicalSurfaceReciprocity

theorem order (X : Scheme) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (W : IrreducibleCloseds X) (hW : Order.coheight (CycleClass.Thom.IntersectionGeometry.supportPoint W) = 1)
    (x : X) (hx : Order.coheight x = 2) (hxW : x ∈ (W : Set X))
    (a b : X.presheaf.stalk x)
    (ha : Local.Principal.supportStalkMap X W x hxW a ≠ 0) (hb : Local.Principal.supportStalkMap X W x hxW b ≠ 0) :
    let Y := CycleClass.Geometric.GenericPoint.reducedSupportScheme W
    let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W x hxW
    let σ := Local.Principal.supportStalkMap X W x hxW
    (Y.ord (algebraMap (Y.presheaf.stalk y) Y.functionField (σ a) /
      algebraMap (Y.presheaf.stalk y) Y.functionField (σ b)) y : ℚ) =
      CanonicalSurfaceReciprocity.restrictedOrder (X.presheaf.stalk x) (Stalk.PrimeQuotient.kernelPrime X W x hxW) a -
        CanonicalSurfaceReciprocity.restrictedOrder (X.presheaf.stalk x) (Stalk.PrimeQuotient.kernelPrime X W x hxW) b := by
  let Y := CycleClass.Geometric.GenericPoint.reducedSupportScheme W
  let y := CycleClass.Thom.IntersectionGeometry.supportPreimage W x hxW
  let σ := Local.Principal.supportStalkMap X W x hxW
  have hy := AdjacentSupportCoheight.coheight_one X W hW x hx hxW
  have haK : algebraMap (Y.presheaf.stalk y) Y.functionField (σ a) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr ha
  have hbK : algebraMap (Y.presheaf.stalk y) Y.functionField (σ b) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hb
  change (Y.ord (_ / _) y : ℚ) = _
  rw [IntrinsicDivisorRatio.Intrinsic.ord_div Y _ _ haK hbK, Int.cast_sub,
    Affine.PrincipalOrder.stalk_order Y y hy _ ha,
    Affine.PrincipalOrder.stalk_order Y y hy _ hb, Int.cast_natCast, Int.cast_natCast]
  have hea := OrderQuotientTransport.ord σ.hom (Local.Principal.supportStalkMap_surjective X W x hxW) a
  have heb := OrderQuotientTransport.ord σ.hom (Local.Principal.supportStalkMap_surjective X W x hxW) b
  exact congrArg₂ (fun n k : ℕ∞ => (n.toNat : ℚ) - (k.toNat : ℚ)) hea heb

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Support.StalkRatioOrder
