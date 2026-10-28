import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Stalk.DivisorRestriction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PositiveCycle

/-! # Unit Divisor Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.UnitDivisorSupport

noncomputable section

/-! A unit in a stalk has no divisor component through that point,
including on singular integral schemes. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem order_zero (Z : Scheme) [IsIntegral Z] [IsLocallyNoetherian Z]
    (x z : Z) (hz : z ⤳ x) (u : Z.presheaf.stalk x) (hu : IsUnit u) :
    Z.ord (algebraMap (Z.presheaf.stalk x) Z.functionField u) z = 0 := by
  by_cases hheight : Order.coheight z = 1
  · have hrange : z ∈ Set.range (Z.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact hz
    obtain ⟨p, hpz⟩ := hrange
    have hp : p.asIdeal.height = 1 := by
      rw [Stalk.Localization.height_eq_coheight_image, hpz]
      exact hheight
    have h := Stalk.DivisorRestriction.order_of_local_element Z x u hu.ne_zero p hp
    rw [hpz, Ring.ord_of_isUnit (hu.map (algebraMap (Z.presheaf.stalk x) (Localization.AtPrime p.asIdeal))),
      ENat.toNat_zero, Int.natCast_zero] at h
    exact h
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hheight _

theorem positive_avoids (Z : Scheme) [IsIntegral Z] [AlgebraicGeometry.IsNoetherian Z]
    (x : Z) (u : Z.presheaf.stalk x) (hu : IsUnit u) (z : Z)
    (hz : z ∈ (PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor Z
      (algebraMap (Z.presheaf.stalk x) Z.functionField u))).support) : ¬ z ⤳ x := by
  intro hs
  apply Finsupp.mem_support_iff.mp hz
  rw [PositiveCycle.positivePart_apply, Affine.DivisorNorm.rationalPrincipalDivisor_apply,
    order_zero Z x z hs u hu, Int.cast_zero, max_self]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.UnitDivisorSupport
