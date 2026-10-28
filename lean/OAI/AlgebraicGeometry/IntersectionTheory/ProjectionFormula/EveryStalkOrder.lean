import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.OrderDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Affine.PrincipalOrder

/-! # Every Stalk Order -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.EveryStalkOrder

noncomputable section

/-! For a nonzero regular germ, the native geometric order at
every point is the natural-number value of its principal colength.
Outside codimension one both sides vanish. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Order

theorem order (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) (r : X.presheaf.stalk x) (hr : r ≠ 0) :
    X.ord (algebraMap (X.presheaf.stalk x) X.functionField r) x =
      ((Ring.ord (X.presheaf.stalk x) r).toNat : ℤ) := by
  by_cases hx : coheight x = 1
  · exact Affine.PrincipalOrder.stalk_order X x hx r hr
  · have hn : (Ring.ord (X.presheaf.stalk x) r).toNat = 0 := by
      by_contra h
      have hd := Finite.OrderDimension.dimension (X.presheaf.stalk x) r hr h
      rw [ringKrullDim_stalk_eq_coheight] at hd
      exact hx (WithBot.coe_inj.mp hd)
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hx, hn, Int.ofNat_zero]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.EveryStalkOrder
