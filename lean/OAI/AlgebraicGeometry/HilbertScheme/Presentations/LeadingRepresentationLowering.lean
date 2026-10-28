import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LeadingCancellation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LeadingTermProductRemainder

/-! # Leading Representation Lowering -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.LeadingRepresentationLowering.GradedHilbert

noncomputable section

/-! A bounded generator representation whose maximal leading terms cancel can be replaced by one with a strictly smaller bound. -/

open _root_.MvPolynomial

universe u v w

variable {K : Type u} [Field K] {n : ℕ}
variable (m : MonomialOrder (Fin (n + 1))) {ι : Type v} (b : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)
variable (hcrit : ∀ i j, m.sPolynomial (b i) (b j) ∈
  LeadingBoundSpans.GradedHilbert.lowerLeadingSpan m b (m.toSyn (m.degree (b i) ⊔ m.degree (b j))))

include hcrit in
theorem bounded_representation_lowering {κ : Type w} (T : Finset κ)
    (idx : κ → ι) (q : κ → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (a : m.syn)
    (hbound : ∀ k ∈ T, q k * b (idx k) = 0 ∨ m.toSyn (m.degree (q k * b (idx k))) ≤ a)
    (hsmall : LeadingBoundSpans.GradedHilbert.leadingBelow m a (∑ k ∈ T, q k * b (idx k))) :
    (∑ k ∈ T, q k * b (idx k)) ∈ LeadingBoundSpans.GradedHilbert.lowerLeadingSpan m b a := by
  classical
  let qtop := fun k => if m.toSyn (m.degree (q k * b (idx k))) = a then q k else 0
  let low := fun k => if m.toSyn (m.degree (q k * b (idx k))) = a
    then (q k - m.leadingTerm (q k)) * b (idx k) else q k * b (idx k)
  have hlow (k : κ) (hk : k ∈ T) : low k ∈ LeadingBoundSpans.GradedHilbert.lowerLeadingSpan m b a := by
    by_cases he : m.toSyn (m.degree (q k * b (idx k))) = a
    · simp only [low, ite_eq_left he]
      apply LeadingBoundSpans.GradedHilbert.mem_lowerLeadingSpan
      rw [← he]
      exact LeadingTermProductRemainder.GradedHilbert.coefficient_leading_remainder_small m (q k) (b (idx k))
    · simp only [low, ite_eq_right he]
      apply LeadingBoundSpans.GradedHilbert.mem_lowerLeadingSpan
      exact (hbound k hk).imp_right (fun h => lt_of_le_of_ne h he)
  have hlowSum : (∑ k ∈ T, low k) ∈ LeadingBoundSpans.GradedHilbert.lowerLeadingSpan m b a := Submodule.sum_mem _ hlow
  have hdecomp : (∑ k ∈ T, q k * b (idx k)) =
      (∑ k ∈ T, low k) + (∑ k ∈ T, m.leadingTerm (qtop k) * b (idx k)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    by_cases he : m.toSyn (m.degree (q k * b (idx k))) = a
    · simp only [low, qtop, ite_eq_left he]
      ring
    · simp only [low, qtop, ite_eq_right he, MonomialOrder.leadingTerm_zero, zero_mul, add_zero]
  have htopBound (k : κ) (_hk : k ∈ T) :
      qtop k * b (idx k) = 0 ∨ m.toSyn (m.degree (qtop k * b (idx k))) = a := by
    by_cases he : m.toSyn (m.degree (q k * b (idx k))) = a
    · exact Or.inr (by simpa only [qtop, ite_eq_left he] using he)
    · exact Or.inl (by simp only [qtop, ite_eq_right he, zero_mul])
  have htopSmall : LeadingBoundSpans.GradedHilbert.leadingBelow m a (∑ k ∈ T, m.leadingTerm (qtop k) * b (idx k)) := by
    have hneg : LeadingBoundSpans.GradedHilbert.leadingBelow m a (-(∑ k ∈ T, low k)) := by
      simpa only [neg_one_smul] using LeadingBoundSpans.GradedHilbert.leadingBelow_smul m a (-1 : K)
        (LeadingBoundSpans.GradedHilbert.leadingBelow_of_mem_lowerLeadingSpan m b a hlowSum)
    have h := LeadingBoundSpans.GradedHilbert.leadingBelow_add m a hsmall hneg
    have he : (∑ k ∈ T, q k * b (idx k)) + -(∑ k ∈ T, low k) =
        ∑ k ∈ T, m.leadingTerm (qtop k) * b (idx k) := by
      rw [hdecomp]
      abel
    rwa [he] at h
  rw [hdecomp]
  exact Submodule.add_mem _ hlowSum
    (LeadingCancellation.GradedHilbert.leading_multiple_sum_cancellation m b hcrit T idx qtop a htopBound htopSmall)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.LeadingRepresentationLowering.GradedHilbert
