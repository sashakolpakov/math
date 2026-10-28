import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.UnitDivisorSupport

/-! # Inverse Divisor Support -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.InverseDivisorSupport

noncomputable section

/-! If the inverse parameter is regular at a point, no zero-divisor
component of the parameter passes through that point. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem order_nonneg (Z : Scheme) [IsIntegral Z] [IsLocallyNoetherian Z]
    (x z : Z) (hz : z ⤳ x) (u : Z.presheaf.stalk x) :
    0 ≤ Z.ord (algebraMap (Z.presheaf.stalk x) Z.functionField u) z := by
  by_cases hu : u = 0
  · simp [hu]
  by_cases hheight : Order.coheight z = 1
  · have hrange : z ∈ Set.range (Z.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact hz
    obtain ⟨p, hpz⟩ := hrange
    have hp : p.asIdeal.height = 1 := by
      rw [Stalk.Localization.height_eq_coheight_image, hpz]
      exact hheight
    rw [← hpz, Stalk.DivisorRestriction.order_of_local_element Z x u hu p hp]
    exact Int.natCast_nonneg _
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hheight]

theorem positive_avoids (Z : Scheme) [IsIntegral Z] [AlgebraicGeometry.IsNoetherian Z]
    (x : Z) (u : Z.presheaf.stalk x) (g : Z.functionField)
    (hu : algebraMap (Z.presheaf.stalk x) Z.functionField u = g⁻¹) (z : Z)
    (hz : z ∈ (PositiveCycle.positivePart (Affine.DivisorNorm.rationalPrincipalDivisor Z g)).support) :
    ¬ z ⤳ x := by
  intro hs
  have hn := order_nonneg Z x z hs u
  rw [hu, Principal.DivisorInverse.ord_inv, neg_nonneg] at hn
  apply Finsupp.mem_support_iff.mp hz
  rw [PositiveCycle.positivePart_apply, Affine.DivisorNorm.rationalPrincipalDivisor_apply]
  exact max_eq_right (by exact_mod_cast hn)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.InverseDivisorSupport
