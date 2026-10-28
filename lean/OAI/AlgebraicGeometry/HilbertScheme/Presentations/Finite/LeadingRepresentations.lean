import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LeadingBoundRepresentations
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.LeadingRepresentationLowering
import Mathlib.Data.List.OfFn

/-! # Leading Representations -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.LeadingRepresentations.GradedHilbert

noncomputable section

/-! Finite generator representations have a leading bound; lower bounded spans provide strictly smaller witnesses. -/

open _root_.MvPolynomial

universe u v

variable {K : Type u} [Field K] {n : ℕ}
variable (m : MonomialOrder (Fin (n + 1))) {ι : Type v} (b : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)

def generatorListValue (L : List (ι × Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n :=
  (L.map (fun t => t.2 * b t.1)).sum

def generatorListBound (L : List (ι × Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) : m.syn := by
  classical
  exact L.toFinset.sup (fun t => m.toSyn (m.degree (t.2 * b t.1)))

theorem exists_ideal_generator_list {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n} (hf : f ∈ Ideal.span (Set.range b)) :
    ∃ L : List (ι × Hilbert.Polynomial.GradedHilbert.CoordinateRing K n), f = generatorListValue b L := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨[(i, 1)], by simp [generatorListValue]⟩
  | zero => exact ⟨[], rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨L, rfl⟩ := hx
    obtain ⟨M, rfl⟩ := hy
    exact ⟨L ++ M, by simp only [generatorListValue, List.map_append, List.sum_append]⟩
  | smul c x _ hx =>
    obtain ⟨L, rfl⟩ := hx
    refine ⟨L.map (fun t => (t.1, c * t.2)), ?_⟩
    change c • (L.map (fun t => t.2 * b t.1)).sum = _
    rw [List.smul_sum]
    simp only [generatorListValue, List.map_map, Function.comp_def, smul_eq_mul, mul_assoc]

theorem generatorListTerm_le_bound (L : List (ι × Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (t : ι × Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)
    (ht : t ∈ L) : m.toSyn (m.degree (t.2 * b t.1)) ≤ generatorListBound m b L := by
  classical
  change m.toSyn (m.degree (t.2 * b t.1)) ≤ L.toFinset.sup (fun s => m.toSyn (m.degree (s.2 * b s.1)))
  exact Finset.le_sup (f := fun s : ι × Hilbert.Polynomial.GradedHilbert.CoordinateRing K n => m.toSyn (m.degree (s.2 * b s.1))) (List.mem_toFinset.mpr ht)

theorem generatorListValue_fin (L : List (ι × Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) :
    generatorListValue b L = ∑ k : Fin L.length, (L.get k).2 * b (L.get k).1 := by
  have he : List.ofFn (fun k : Fin L.length => (L.get k).2 * b (L.get k).1) =
      L.map (fun t => t.2 * b t.1) := by
    rw [List.ofFn_comp' L.get (fun t : ι × Hilbert.Polynomial.GradedHilbert.CoordinateRing K n => t.2 * b t.1), List.ofFn_get]
  rw [generatorListValue, ← he, List.sum_ofFn]

theorem generatorListValue_degree_le (L : List (ι × Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) :
    m.toSyn (m.degree (generatorListValue b L)) ≤ generatorListBound m b L := by
  classical
  rw [generatorListValue_fin]
  apply m.degree_sum_le.trans
  apply Finset.sup_le
  intro k _
  exact generatorListTerm_le_bound m b L (L.get k) (List.get_mem L k)

theorem lowerLeadingSpan_exists_smaller_bound (a : m.syn) {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n}
    (hf : f ∈ LeadingBoundSpans.GradedHilbert.lowerLeadingSpan m b a) (hf0 : f ≠ 0) :
    ∃ L : List (ι × Hilbert.Polynomial.GradedHilbert.CoordinateRing K n), f = generatorListValue b L ∧ generatorListBound m b L < a := by
  classical
  obtain ⟨L, hL, hLb⟩ := LeadingBoundRepresentations.GradedHilbert.lowerLeadingSpan_exists_list m b a hf
  have hfa : m.toSyn (m.degree f) < a := (LeadingBoundSpans.GradedHilbert.leadingBelow_of_mem_lowerLeadingSpan m b a hf).resolve_left hf0
  have ha : (⊥ : m.syn) < a := bot_le.trans_lt hfa
  refine ⟨L, hL, (Finset.sup_lt_iff ha).mpr ?_⟩
  intro t ht
  rcases hLb t (List.mem_toFinset.mp ht) with hz | hlt
  · simpa only [hz, MonomialOrder.degree_zero, map_zero, m.bot_eq_zero] using ha
  · exact hlt

variable (hcrit : ∀ i j, m.sPolynomial (b i) (b j) ∈
  LeadingBoundSpans.GradedHilbert.lowerLeadingSpan m b (m.toSyn (m.degree (b i) ⊔ m.degree (b j))))

include hcrit in
theorem generatorList_lowering (L : List (ι × Hilbert.Polynomial.GradedHilbert.CoordinateRing K n))
    (hsmall : LeadingBoundSpans.GradedHilbert.leadingBelow m (generatorListBound m b L) (generatorListValue b L)) :
    generatorListValue b L ∈ LeadingBoundSpans.GradedHilbert.lowerLeadingSpan m b (generatorListBound m b L) := by
  rw [generatorListValue_fin] at hsmall ⊢
  apply LeadingRepresentationLowering.GradedHilbert.bounded_representation_lowering m b hcrit Finset.univ
    (fun k : Fin L.length => (L.get k).1) (fun k => (L.get k).2) _ _ hsmall
  intro k _
  exact Or.inr (generatorListTerm_le_bound m b L (L.get k) (List.get_mem L k))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.LeadingRepresentations.GradedHilbert
