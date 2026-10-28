import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.FiniteDivision

/-! # Leading Bound Spans -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.LeadingBoundSpans.GradedHilbert

noncomputable section

/-! Spans of generator multiples with a strict leading-term bound, including stability under multiplication. -/

open _root_.MvPolynomial
open scoped MonomialOrder

universe u v

variable {K : Type u} [Field K] {n : ℕ}
variable (m : MonomialOrder (Fin (n + 1))) {ι : Type v} (b : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)

def leadingBelow (a : m.syn) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) : Prop :=
  f = 0 ∨ m.toSyn (m.degree f) < a

def lowerLeadingSpan (a : m.syn) : Submodule K (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) :=
  Submodule.span K {f | ∃ i q, f = q * b i ∧ leadingBelow m a f}

theorem leadingBelow_add (a : m.syn) {f g : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n}
    (hf : leadingBelow m a f) (hg : leadingBelow m a g) : leadingBelow m a (f + g) := by
  rcases hf with rfl | hf
  · simpa only [zero_add] using hg
  rcases hg with rfl | hg
  · exact Or.inr (by simpa only [add_zero] using hf)
  exact Or.inr (m.degree_add_le.trans_lt (sup_lt_iff.mpr ⟨hf, hg⟩))

theorem leadingBelow_smul (a : m.syn) (c : K) {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n}
    (hf : leadingBelow m a f) : leadingBelow m a (c • f) := by
  rcases hf with rfl | hf
  · exact Or.inl (smul_zero c)
  · exact Or.inr (m.degree_smul_le.trans_lt hf)

theorem leadingBelow_mul (a : m.syn) (p : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n}
    (hf : leadingBelow m a f) : leadingBelow m (m.toSyn (m.degree p) + a) (p * f) := by
  rcases hf with rfl | hf
  · exact Or.inl (mul_zero p)
  · exact Or.inr (m.degree_mul_le.trans_lt (by simpa only [map_add, add_comm] using add_lt_add_left hf (m.toSyn (m.degree p))))

theorem mem_lowerLeadingSpan (a : m.syn) (i : ι) (q : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)
    (hq : leadingBelow m a (q * b i)) : q * b i ∈ lowerLeadingSpan m b a :=
  Submodule.subset_span ⟨i, q, rfl, hq⟩

theorem lowerLeadingSpan_mono {a c : m.syn} (hac : a ≤ c) : lowerLeadingSpan m b a ≤ lowerLeadingSpan m b c := by
  apply Submodule.span_mono
  rintro f ⟨i, q, rfl, hq⟩
  exact ⟨i, q, rfl, hq.imp_right (fun h => h.trans_le hac)⟩

theorem leadingBelow_of_mem_lowerLeadingSpan (a : m.syn) {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n}
    (hf : f ∈ lowerLeadingSpan m b a) : leadingBelow m a f := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact hx.choose_spec.choose_spec.2
  | zero => exact Or.inl rfl
  | add x y _ _ hx hy => exact leadingBelow_add m a hx hy
  | smul c x _ hx => exact leadingBelow_smul m a c hx

theorem mul_mem_lowerLeadingSpan (a : m.syn) (p : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n}
    (hf : f ∈ lowerLeadingSpan m b a) : p * f ∈ lowerLeadingSpan m b (m.toSyn (m.degree p) + a) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, q, rfl, hq⟩ := hx
    rw [← mul_assoc]
    exact mem_lowerLeadingSpan m b _ i (p * q) (by rw [mul_assoc]; exact leadingBelow_mul m a p hq)
  | zero => simpa only [mul_zero] using (lowerLeadingSpan m b _).zero_mem
  | add x y _ _ hx hy => simpa only [mul_add] using (lowerLeadingSpan m b _).add_mem hx hy
  | smul c x _ hx => simpa only [mul_smul_comm] using (lowerLeadingSpan m b _).smul_mem c hx

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.LeadingBoundSpans.GradedHilbert
