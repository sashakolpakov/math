import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.GroebnerCompletion

/-! # Initial Generators -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Bounded.InitialGenerators.GradedHilbert

noncomputable section

/-! Bounded homogeneous generators give a field-independent degree bound for generators of the actual initial ideal. -/

open _root_.MvPolynomial

universe u v

variable {K : Type u} [Field K] {n : ℕ}
variable (m : MonomialOrder (Fin (n + 1)))

theorem initialIdeal_eq_of_leading_cover {ι : Type v} (c : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)
    (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) (hc : ∀ i, c i ∈ I ∧ c i ≠ 0)
    (hcover : ∀ f ∈ I, f ≠ 0 → ∃ i, m.degree (c i) ≤ m.degree f) :
    InitialIdeal.GradedHilbert.initialIdeal m I = Ideal.span (Set.range (fun i => monomial (m.degree (c i)) (1 : K))) := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, ⟨f, ⟨hf, hf0⟩, rfl⟩, rfl⟩
    obtain ⟨i, hi⟩ := hcover f hf hf0
    have h := (Ideal.span (Set.range (fun j => monomial (m.degree (c j)) (1 : K)))).mul_mem_left
      (monomial (m.degree f - m.degree (c i)) (1 : K)) (Ideal.subset_span (Set.mem_range_self i))
    change monomial (m.degree f) (1 : K) ∈ Ideal.span (Set.range (fun j => monomial (m.degree (c j)) (1 : K)))
    simpa only [monomial_mul_monomial, one_mul, tsub_add_cancel_of_le hi] using h
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact InitialIdeal.GradedHilbert.leading_monomial_mem_initialIdeal m (hc i).1 (hc i).2

theorem exists_uniform_initial_generators
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (B : Finset (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n))
    (hB : I.toIdeal = Ideal.span (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)))
    (D : ℕ) (hb : ∀ b ∈ B, b ≠ 0 ∧ ∃ d ≤ D, b.IsHomogeneous d) :
    ∃ G : Finset (Fin (n + 1) →₀ ℕ),
      InitialIdeal.GradedHilbert.initialIdeal m I.toIdeal = Ideal.span ((fun a => monomial a (1 : K)) '' (G : Set (Fin (n + 1) →₀ ℕ))) ∧
      ∀ a ∈ G, a.degree ≤ Uniform.GroebnerCompletion.GradedHilbert.homogeneousGroebnerDegreeBound n D := by
  classical
  choose e he hh using fun b : B => (hb b.val b.property).2
  obtain ⟨k, c, hspan, hc, hcover⟩ := Uniform.GroebnerCompletion.GradedHilbert.exists_uniform_homogeneous_groebner_completion m
    (fun b : B => b.val) e hh (fun b => (hb b.val b.property).1) D he
  have hB' : Set.range (fun b : B => b.val) = (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) := Subtype.range_coe_subtype
  have hI : Ideal.span (Set.range c) = I.toIdeal := by rw [hspan, hB', ← hB]
  let G := Finset.univ.image (fun j => m.degree (c j))
  refine ⟨G, ?_, ?_⟩
  · rw [initialIdeal_eq_of_leading_cover m c I.toIdeal (fun j => ⟨by
      rw [← hI]
      exact Ideal.subset_span (Set.mem_range_self j), (hc j).1⟩) (by simpa only [hB', ← hB] using hcover)]
    apply congrArg Ideal.span
    ext a
    simp only [G, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range, Set.mem_image]
    aesop
  · intro a ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨d, hd, hhom⟩ := (hc j).2
    rw [Homogeneous.Polynomials.GradedHilbert.homogeneous_leadingDegree m hhom (hc j).1]
    exact hd

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Bounded.InitialGenerators.GradedHilbert
