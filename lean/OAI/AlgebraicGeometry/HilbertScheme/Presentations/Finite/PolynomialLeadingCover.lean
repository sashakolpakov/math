import OAI.AlgebraicGeometry.HilbertScheme.Presentations.InitialIdeal

/-! # Polynomial Leading Cover -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.PolynomialLeadingCover.GradedHilbert

noncomputable section

/-! Every polynomial ideal over a field has a finite leading-term cover,
without a homogeneity assumption. -/

open _root_.MvPolynomial

universe u
variable {K : Type u} [Field K] {n : ℕ}

theorem exists_finite_polynomial_leading_cover (m : MonomialOrder (Fin (n + 1)))
    (I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) :
    ∃ B : Finset (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n),
      (∀ b ∈ B, b ∈ I ∧ b ≠ 0) ∧
      ∀ f ∈ I, f ≠ 0 → ∃ b ∈ B, m.degree b ≤ m.degree f := by
  classical
  obtain ⟨G, hG⟩ := (InitialIdeal.GradedHilbert.initialIdeal_isMonomial m I).finite_generators
  have hlift (a : G) : ∃ b : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n,
      b ∈ I ∧ b ≠ 0 ∧ m.degree b ≤ a.val := by
    apply (InitialIdeal.GradedHilbert.monomial_mem_initialIdeal_iff m I a.val).mp
    rw [hG]
    exact Ideal.subset_span ⟨a.val, a.property, rfl⟩
  choose b hb using hlift
  let B := Finset.univ.image b
  refine ⟨B, ?_, ?_⟩
  · intro f hf
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hf
    exact ⟨(hb a).1, (hb a).2.1⟩
  · intro f hf hf0
    have hlead := InitialIdeal.GradedHilbert.leading_monomial_mem_initialIdeal m hf hf0
    rw [hG, mem_ideal_span_monomial_image] at hlead
    have hm : m.degree f ∈ (monomial (m.degree f) (1 : K)).support := by simp
    obtain ⟨a, ha, haf⟩ := hlead (m.degree f) hm
    exact ⟨b ⟨a, ha⟩, Finset.mem_image.mpr ⟨⟨a, ha⟩, Finset.mem_univ _, rfl⟩,
      (hb ⟨a, ha⟩).2.2.trans haf⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.PolynomialLeadingCover.GradedHilbert
