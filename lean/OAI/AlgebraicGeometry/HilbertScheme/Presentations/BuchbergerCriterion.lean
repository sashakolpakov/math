import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.LeadingRepresentations

/-! # Buchberger Criterion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BuchbergerCriterion.GradedHilbert

noncomputable section

/-! The critical-pair criterion for actual polynomial ideals: strict bounded representations of the generator S-polynomials imply a leading-monomial cover of the ideal. -/

open _root_.MvPolynomial

universe u v

variable {K : Type u} [Field K] {n : ℕ}
variable (m : MonomialOrder (Fin (n + 1))) {ι : Type v} (b : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)
variable (hcrit : ∀ i j, m.sPolynomial (b i) (b j) ∈
  LeadingBoundSpans.GradedHilbert.lowerLeadingSpan m b (m.toSyn (m.degree (b i) ⊔ m.degree (b j))))

include hcrit in
theorem buchberger_leading_cover {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n}
    (hf : f ∈ Ideal.span (Set.range b)) (hf0 : f ≠ 0) :
    ∃ i, m.degree (b i) ≤ m.degree f := by
  classical
  obtain ⟨L, hmin⟩ := exists_minimalFor_of_wellFoundedLT
    (fun L : List (ι × Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) => f = Finite.LeadingRepresentations.GradedHilbert.generatorListValue b L)
    (Finite.LeadingRepresentations.GradedHilbert.generatorListBound m b) (Finite.LeadingRepresentations.GradedHilbert.exists_ideal_generator_list b hf)
  have hrep := hmin.prop
  have hle : m.toSyn (m.degree f) ≤ Finite.LeadingRepresentations.GradedHilbert.generatorListBound m b L := by
    rw [hrep]
    exact Finite.LeadingRepresentations.GradedHilbert.generatorListValue_degree_le m b L
  have hbound : Finite.LeadingRepresentations.GradedHilbert.generatorListBound m b L = m.toSyn (m.degree f) := by
    apply le_antisymm _ hle
    apply le_of_not_gt
    intro hlt
    have hsmall : LeadingBoundSpans.GradedHilbert.leadingBelow m (Finite.LeadingRepresentations.GradedHilbert.generatorListBound m b L) (Finite.LeadingRepresentations.GradedHilbert.generatorListValue b L) := by
      rw [← hrep]
      exact Or.inr hlt
    have hmem : f ∈ LeadingBoundSpans.GradedHilbert.lowerLeadingSpan m b (Finite.LeadingRepresentations.GradedHilbert.generatorListBound m b L) := by
      rw [hrep]
      exact Finite.LeadingRepresentations.GradedHilbert.generatorList_lowering m b hcrit L hsmall
    obtain ⟨M, hM, hMb⟩ := Finite.LeadingRepresentations.GradedHilbert.lowerLeadingSpan_exists_smaller_bound m b _ hmem hf0
    exact (hmin.not_lt hM) hMb
  by_contra! hnot
  have hsum : (∑ k : Fin L.length, (L.get k).2 * b (L.get k).1) ∈
      LeadingBoundSpans.GradedHilbert.lowerLeadingSpan m b (m.toSyn (m.degree f)) := by
    apply Submodule.sum_mem
    intro k _
    let t := L.get k
    apply LeadingBoundSpans.GradedHilbert.mem_lowerLeadingSpan m b _ t.1 t.2
    by_cases ht0 : t.2 * b t.1 = 0
    · exact Or.inl ht0
    · apply Or.inr
      have htbound : m.toSyn (m.degree (t.2 * b t.1)) ≤ m.toSyn (m.degree f) :=
        (Finite.LeadingRepresentations.GradedHilbert.generatorListTerm_le_bound m b L t (List.get_mem L k)).trans hbound.le
      apply lt_of_le_of_ne htbound
      intro heq
      have he : m.degree (t.2 * b t.1) = m.degree f := m.toSyn.injective heq
      have ht2 : t.2 ≠ 0 := fun hz => ht0 (by rw [hz, zero_mul])
      have hbt : b t.1 ≠ 0 := fun hz => ht0 (by rw [hz, mul_zero])
      apply hnot t.1
      rw [← he, m.degree_mul ht2 hbt]
      exact le_add_left le_rfl
  have hmem : f ∈ LeadingBoundSpans.GradedHilbert.lowerLeadingSpan m b (m.toSyn (m.degree f)) := by
    simpa only [← Finite.LeadingRepresentations.GradedHilbert.generatorListValue_fin, ← hrep] using hsum
  rcases LeadingBoundSpans.GradedHilbert.leadingBelow_of_mem_lowerLeadingSpan m b _ hmem with hz | hlt
  · exact hf0 hz
  · exact lt_irrefl _ hlt

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BuchbergerCriterion.GradedHilbert
