import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LeadingBoundSpans

/-! # Critical Pair Multiples -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.CriticalPairMultiples.GradedHilbert

noncomputable section

/-! Reductions of generator critical pairs also reduce critical pairs of their equal-leading-term multiples. -/

open _root_.MvPolynomial

universe u v

variable {K : Type u} [Field K] {n : ℕ}
variable (m : MonomialOrder (Fin (n + 1))) {ι : Type v} (b : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)
variable (hcrit : ∀ i j, m.sPolynomial (b i) (b j) ∈
  LeadingBoundSpans.GradedHilbert.lowerLeadingSpan m b (m.toSyn (m.degree (b i) ⊔ m.degree (b j))))

include hcrit in
theorem criticalPair_leading_multiples_mem (a : m.syn) (i j : ι) (p q : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)
    (hi : p * b i = 0 ∨ m.toSyn (m.degree (p * b i)) = a)
    (hj : q * b j = 0 ∨ m.toSyn (m.degree (q * b j)) = a) :
    m.sPolynomial (m.leadingTerm p * b i) (m.leadingTerm q * b j) ∈ LeadingBoundSpans.GradedHilbert.lowerLeadingSpan m b a := by
  by_cases hi0 : p * b i = 0
  · obtain hp | hb := mul_eq_zero.mp hi0
    · simp only [hp, MonomialOrder.leadingTerm_zero, zero_mul, MonomialOrder.sPolynomial_left_zero]
      exact Submodule.zero_mem _
    · simp only [hb, mul_zero, MonomialOrder.sPolynomial_left_zero]
      exact Submodule.zero_mem _
  by_cases hj0 : q * b j = 0
  · obtain hq | hb := mul_eq_zero.mp hj0
    · simp only [hq, MonomialOrder.leadingTerm_zero, zero_mul, MonomialOrder.sPolynomial_right_zero]
      exact Submodule.zero_mem _
    · simp only [hb, mul_zero, MonomialOrder.sPolynomial_right_zero]
      exact Submodule.zero_mem _
  have hp0 : p ≠ 0 := fun hp => hi0 (by rw [hp, zero_mul])
  have hbi0 : b i ≠ 0 := fun hb => hi0 (by rw [hb, mul_zero])
  have hq0 : q ≠ 0 := fun hq => hj0 (by rw [hq, zero_mul])
  have hbj0 : b j ≠ 0 := fun hb => hj0 (by rw [hb, mul_zero])
  have hi' : m.degree (p * b i) = m.toSyn.symm a :=
    m.toSyn.injective ((hi.resolve_left hi0).trans (m.toSyn.apply_symm_apply a).symm)
  have hj' : m.degree (q * b j) = m.toSyn.symm a :=
    m.toSyn.injective ((hj.resolve_left hj0).trans (m.toSyn.apply_symm_apply a).symm)
  have hbi : m.degree (b i) ≤ m.toSyn.symm a := by
    rw [← hi', m.degree_mul hp0 hbi0]
    exact le_add_left le_rfl
  have hbj : m.degree (b j) ≤ m.toSyn.symm a := by
    rw [← hj', m.degree_mul hq0 hbj0]
    exact le_add_left le_rfl
  have hle : m.degree (b i) ⊔ m.degree (b j) ≤ m.toSyn.symm a := sup_le hbi hbj
  rw [m.sPolynomial_leadingTerm_mul', hi', hj', sup_idem]
  apply LeadingBoundSpans.GradedHilbert.lowerLeadingSpan_mono m b ?_ (LeadingBoundSpans.GradedHilbert.mul_mem_lowerLeadingSpan m b _ _ (hcrit i j))
  calc
    _ ≤ m.toSyn (m.toSyn.symm a - (m.degree (b i) ⊔ m.degree (b j))) +
        m.toSyn (m.degree (b i) ⊔ m.degree (b j)) :=
      add_le_add (m.degree_monomial_le _) le_rfl
    _ = a := by rw [← map_add, tsub_add_cancel_of_le hle, m.toSyn.apply_symm_apply]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.CriticalPairMultiples.GradedHilbert
