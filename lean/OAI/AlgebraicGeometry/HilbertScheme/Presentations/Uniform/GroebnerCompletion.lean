import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ControlledCompletionCertificates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CriticalPairRemainders
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BuchbergerCriterion
import Mathlib.Data.Nat.Find

/-! # Groebner Completion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.GroebnerCompletion.GradedHilbert

noncomputable section

/-! A field-independent homogeneous Gröbner degree bound, obtained from controlled critical-pair completion and Dickson's lemma. -/

open _root_.MvPolynomial

universe u v

def homogeneousGroebnerDegreeBound (n D : ℕ) : ℕ := D * 2 ^ ControlledCompletionCertificates.GradedHilbert.polynomialCompletionHorizon n D

variable {K : Type u} [Field K] {n : ℕ}
variable (m : MonomialOrder (Fin (n + 1))) {ι : Type v} [Fintype ι]
variable (b : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) (e : ι → ℕ)

theorem exists_uniform_homogeneous_groebner_completion
    (hb : ∀ i, (b i).IsHomogeneous (e i)) (hb0 : ∀ i, b i ≠ 0)
    (D : ℕ) (hD : ∀ i, e i ≤ D) :
    ∃ k : ℕ, ∃ c : ι ⊕ Fin k → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n,
      Ideal.span (Set.range c) = Ideal.span (Set.range b) ∧
      (∀ j, c j ≠ 0 ∧ ∃ d ≤ homogeneousGroebnerDegreeBound n D, (c j).IsHomogeneous d) ∧
      ∀ f ∈ Ideal.span (Set.range b), f ≠ 0 → ∃ j, m.degree (c j) ≤ m.degree f := by
  classical
  let I := Ideal.span (Set.range b)
  let H := ControlledCompletionCertificates.GradedHilbert.polynomialCompletionHorizon n D
  let P := fun k => Nonempty (ControlledCompletionCertificates.GradedHilbert.ControlledCompletionCertificate m I D k)
  let k := Nat.findGreatest P H
  have hk : P k := Nat.findGreatest_spec (m := 0) (Nat.zero_le H)
    (⟨ControlledCompletionCertificates.GradedHilbert.ControlledCompletionCertificate.empty m I D⟩ : P 0)
  obtain ⟨C⟩ := hk
  have hkH : k < H := C.length_lt
  let c : ι ⊕ Fin k → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n := Sum.elim b C.value
  have hc0 : ∀ j, c j ≠ 0 := by
    intro j
    exact Sum.rec hb0 C.nonzero j
  have hcI : ∀ j, c j ∈ I := by
    intro j
    exact Sum.rec (fun i => Ideal.subset_span (Set.mem_range_self i)) C.mem_ideal j
  have hspan : Ideal.span (Set.range c) = I := by
    apply le_antisymm
    · exact Ideal.span_le.mpr (by rintro f ⟨j, rfl⟩; exact hcI j)
    · apply Ideal.span_le.mpr
      rintro f ⟨j, rfl⟩
      exact Ideal.subset_span (Set.mem_range.mpr ⟨Sum.inl j, rfl⟩)
  have hcHom : ∀ j, ∃ d ≤ D * 2 ^ k, (c j).IsHomogeneous d := by
    intro j
    cases j with
    | inl i => exact ⟨e i, (hD i).trans (Nat.le_mul_of_pos_right D (pow_pos (by decide) k)), hb i⟩
    | inr i =>
      obtain ⟨d, hd, hhom⟩ := C.homogeneous i
      exact ⟨d, hd.trans (Nat.mul_le_mul_left D (Nat.pow_le_pow_right (by decide) (by omega))), hhom⟩
  choose ec hec hc using hcHom
  have hcrit : ∀ i j, m.sPolynomial (c i) (c j) ∈
      LeadingBoundSpans.GradedHilbert.lowerLeadingSpan m c (m.toSyn (m.degree (c i) ⊔ m.degree (c j))) := by
    by_contra! hnot
    obtain ⟨i, j, hij⟩ := hnot
    obtain ⟨d, hd, r, hrhom, hrI, hcorr, hrred⟩ := CriticalPairRemainders.GradedHilbert.criticalPair_homogeneous_remainder m c ec hc hc0
      (D * 2 ^ k) hec i j
    have hr0 : r ≠ 0 := by
      intro hz
      exact hij (by simpa only [hz, sub_zero] using hcorr)
    have hrI' : r ∈ I := hspan ▸ hrI
    have hrbound : d ≤ D * 2 ^ (k + 1) := by
      simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hd
    have hrnew : ∀ a, ¬ m.degree (C.value a) ≤ m.degree r :=
      fun a => hrred (m.degree r) (m.degree_mem_support hr0) (Sum.inr a)
    let C' := ControlledCompletionCertificates.GradedHilbert.ControlledCompletionCertificate.append m I D C r hr0 hrI' ⟨d, hrbound, hrhom⟩ hrnew
    have hnext : k + 1 ≤ k := Nat.le_findGreatest (P := P) (Nat.succ_le_of_lt hkH) ⟨C'⟩
    omega
  refine ⟨k, c, hspan, ?_, ?_⟩
  · intro j
    refine ⟨hc0 j, ec j, (hec j).trans ?_, hc j⟩
    exact Nat.mul_le_mul_left D (Nat.pow_le_pow_right (by decide) hkH.le)
  · intro f hf hf0
    apply BuchbergerCriterion.GradedHilbert.buchberger_leading_cover m c hcrit _ hf0
    rwa [hspan]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.GroebnerCompletion.GradedHilbert
