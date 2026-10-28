import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LeadingBoundSpans

/-! # Leading Term Product Remainder -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.LeadingTermProductRemainder.GradedHilbert

noncomputable section

/-! Removing the leading term of a coefficient lowers the leading bound of its generator multiple. -/

open _root_.MvPolynomial

universe u

variable {K : Type u} [Field K] {n : ℕ}
variable (m : MonomialOrder (Fin (n + 1)))

theorem coefficient_leading_remainder_small (p b : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) :
    LeadingBoundSpans.GradedHilbert.leadingBelow m (m.toSyn (m.degree (p * b))) ((p - m.leadingTerm p) * b) := by
  by_cases hb : b = 0
  · exact Or.inl (by rw [hb, mul_zero])
  by_cases hp : p - m.leadingTerm p = 0
  · exact Or.inl (by rw [hp, zero_mul])
  have hpdeg : m.degree p ≠ 0 := m.degree_ne_zero_of_sub_leadingTerm_ne_zero hp
  have hp0 : p ≠ 0 := m.ne_zero_of_degree_ne_zero hpdeg
  apply Or.inr
  have hlt := m.degree_sub_leadingTerm_lt_degree hpdeg
  apply m.degree_mul_le.trans_lt
  rw [m.degree_mul hp0 hb, map_add, map_add]
  exact add_lt_add_left hlt _

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.LeadingTermProductRemainder.GradedHilbert
