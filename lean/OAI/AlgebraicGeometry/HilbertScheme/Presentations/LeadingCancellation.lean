import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CriticalPairMultiples

/-! # Leading Cancellation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.LeadingCancellation.GradedHilbert

noncomputable section

/-! Cancellation of maximal leading terms is controlled by the finitely many generator critical pairs. -/

open _root_.MvPolynomial

universe u v w

variable {K : Type u} [Field K] {n : ℕ}
variable (m : MonomialOrder (Fin (n + 1))) {ι : Type v} (b : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)
variable (hcrit : ∀ i j, m.sPolynomial (b i) (b j) ∈
  LeadingBoundSpans.GradedHilbert.lowerLeadingSpan m b (m.toSyn (m.degree (b i) ⊔ m.degree (b j))))

include hcrit in
theorem leading_multiple_sum_cancellation {κ : Type w} (T : Finset κ)
    (idx : κ → ι) (q : κ → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (a : m.syn)
    (hmax : ∀ k ∈ T, q k * b (idx k) = 0 ∨ m.toSyn (m.degree (q k * b (idx k))) = a)
    (hsmall : LeadingBoundSpans.GradedHilbert.leadingBelow m a (∑ k ∈ T, m.leadingTerm (q k) * b (idx k))) :
    (∑ k ∈ T, m.leadingTerm (q k) * b (idx k)) ∈ LeadingBoundSpans.GradedHilbert.lowerLeadingSpan m b a := by
  classical
  by_cases hz : (∑ k ∈ T, m.leadingTerm (q k) * b (idx k)) = 0
  · rw [hz]
    exact Submodule.zero_mem _
  have hdeg (k : κ) (hk : k ∈ T) :
      m.toSyn (m.degree (m.leadingTerm (q k) * b (idx k))) = a ∨ m.leadingTerm (q k) * b (idx k) = 0 := by
    rcases hmax k hk with hzero | heq
    · right
      simpa only [mul_eq_zero, MonomialOrder.leadingTerm_eq_zero_iff] using hzero
    · left
      simpa only [m.degree_leadingTerm_mul] using heq
  obtain ⟨c, hc⟩ := m.sPolynomial_decomposition'
    (fun k => m.leadingTerm (q k) * b (idx k)) hdeg (hsmall.resolve_left hz)
  rw [hc]
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.sum_mem
  intro l hl
  apply Submodule.smul_mem
  exact CriticalPairMultiples.GradedHilbert.criticalPair_leading_multiples_mem m b hcrit a (idx k) (idx l) (q k) (q l)
    (hmax k hk) (hmax l hl)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.LeadingCancellation.GradedHilbert
