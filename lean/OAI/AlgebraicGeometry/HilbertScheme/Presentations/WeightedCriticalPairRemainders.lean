import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LeadingBoundSpans
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedFiniteDivision

/-! # Weighted Critical Pair Remainders -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedCriticalPairRemainders.GradedHilbert

noncomputable section

/-! Critical-pair division produces a controlled homogeneous remainder and a strictly lower leading-term representation of the correction. -/

open _root_.MvPolynomial
open scoped MonomialOrder

universe u v

variable {K : Type u} [Field K] {n : ℕ}
variable (w : Fin (n + 1) → ℕ) (m : MonomialOrder (Fin (n + 1)))
variable {ι : Type v} [Fintype ι] (b : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (e : ι → ℕ)

theorem criticalPair_weighted_homogeneous_remainder (hb : ∀ i, (b i).IsWeightedHomogeneous w (e i))
    (hb0 : ∀ i, b i ≠ 0) (D : ℕ) (hD : ∀ i, e i ≤ D) (i j : ι) :
    ∃ d ≤ 2 * D, ∃ r : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n,
      r.IsWeightedHomogeneous w d ∧ r ∈ Ideal.span (Set.range b) ∧
      (m.sPolynomial (b i) (b j) - r) ∈ LeadingBoundSpans.GradedHilbert.lowerLeadingSpan m b (m.toSyn (m.degree (b i) ⊔ m.degree (b j))) ∧
      ∀ a ∈ r.support, ∀ k, ¬ m.degree (b k) ≤ a := by
  let d := Finsupp.weight w (m.degree (b i) ⊔ m.degree (b j))
  have hDi := hD i
  have hDj := hD j
  have hd : d ≤ 2 * D := (WeightedPolynomials.GradedHilbert.sPolynomial_weighted_degree_bound w m (hb i) (hb j) (hb0 i) (hb0 j)).trans (by omega)
  have hhom : (m.sPolynomial (b i) (b j)).IsWeightedHomogeneous w d :=
    WeightedPolynomials.GradedHilbert.sPolynomial_weighted_homogeneous w m (hb i) (hb j) (hb0 i) (hb0 j)
  by_cases hzero : m.sPolynomial (b i) (b j) = 0
  · refine ⟨d, hd, 0, isWeightedHomogeneous_zero K w d, Ideal.zero_mem _, ?_, ?_⟩
    · rw [hzero, sub_zero]
      exact Submodule.zero_mem _
    · intro a ha
      exact (Finset.notMem_empty a ha).elim
  · obtain ⟨q, r, hrep, hrhom, hq, hr⟩ := WeightedFiniteDivision.GradedHilbert.weighted_homogeneous_finite_division w m b e hb hb0 _ d hhom
    have hsum : (∑ k, q k * b k) ∈ Ideal.span (Set.range b) :=
      Ideal.sum_mem _ (fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self k)))
    have hrmem : r ∈ Ideal.span (Set.range b) := by
      have hs := Homogeneous.Polynomials.GradedHilbert.sPolynomial_mem_ideal m (I := Ideal.span (Set.range b)) (f := b i) (g := b j)
        (Ideal.subset_span (Set.mem_range_self i)) (Ideal.subset_span (Set.mem_range_self j))
      have ht := (Ideal.span (Set.range b)).sub_mem hs hsum
      simpa only [hrep, add_sub_cancel_left] using ht
    refine ⟨d, hd, r, hrhom, hrmem, ?_, hr⟩
    rw [hrep, add_sub_cancel_right]
    apply Submodule.sum_mem
    intro k _
    exact LeadingBoundSpans.GradedHilbert.mem_lowerLeadingSpan m b _ k (q k) (Or.inr
      ((hq k).trans_lt (m.degree_sPolynomial_lt_sup_degree hzero)))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.WeightedCriticalPairRemainders.GradedHilbert
