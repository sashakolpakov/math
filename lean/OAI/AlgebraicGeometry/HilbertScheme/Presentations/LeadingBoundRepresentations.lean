import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LeadingBoundSpans

/-! # Leading Bound Representations -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.LeadingBoundRepresentations.GradedHilbert

noncomputable section

/-! Membership in a bounded leading-term span has a finite list of actual generator multiples as a witness. -/

open _root_.MvPolynomial

universe u v

variable {K : Type u} [Field K] {n : ℕ}
variable (m : MonomialOrder (Fin (n + 1))) {ι : Type v} (b : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)

theorem lowerLeadingSpan_exists_list (a : m.syn) {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n}
    (hf : f ∈ LeadingBoundSpans.GradedHilbert.lowerLeadingSpan m b a) :
    ∃ L : List (ι × Hilbert.Polynomial.GradedHilbert.CoordinateRing K n),
      f = (L.map (fun t => t.2 * b t.1)).sum ∧
      ∀ t ∈ L, LeadingBoundSpans.GradedHilbert.leadingBelow m a (t.2 * b t.1) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, q, rfl, hq⟩ := hx
    exact ⟨[(i, q)], by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero],
      fun t ht => (List.mem_singleton.mp ht) ▸ hq⟩
  | zero => exact ⟨[], rfl, by simp only [List.not_mem_nil, false_implies, implies_true]⟩
  | add x y _ _ hx hy =>
    obtain ⟨L, hL, hLb⟩ := hx
    obtain ⟨M, hM, hMb⟩ := hy
    refine ⟨L ++ M, ?_, fun t ht => ?_⟩
    · rw [List.map_append, List.sum_append, ← hL, ← hM]
    · exact (List.mem_append.mp ht).elim (hLb t) (hMb t)
  | smul c x _ hx =>
    obtain ⟨L, hL, hLb⟩ := hx
    refine ⟨L.map (fun t => (t.1, c • t.2)), ?_, ?_⟩
    · rw [hL, List.smul_sum, List.map_map, List.map_map]
      simp only [Function.comp_def, smul_mul_assoc]
    · intro t ht
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
      change LeadingBoundSpans.GradedHilbert.leadingBelow m a ((c • s.2) * b s.1)
      rw [smul_mul_assoc]
      exact LeadingBoundSpans.GradedHilbert.leadingBelow_smul m a c (hLb s hs)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.LeadingBoundRepresentations.GradedHilbert
