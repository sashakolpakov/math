import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.MonomialBasis

/-! # Monomial Bound -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.MonomialBound.GradedHilbert

noncomputable section

/-!
Field-independent saturation for monomial ideals and a generator-degree
bound depending only on the number of variables and the Hilbert polynomial.
-/

open _root_.MvPolynomial

universe u v

variable {n : ℕ} {K : Type u} [Field K]

theorem monomial_mem_monomialSpan_iff (S : Set (Fin (n + 1) →₀ ℕ))
    (a : Fin (n + 1) →₀ ℕ) :
    monomial a (1 : K) ∈ (Hilbert.MonomialBasis.GradedHilbert.monomialSpan K S).toIdeal ↔ ∃ b ∈ S, b ≤ a := by
  classical
  change monomial a (1 : K) ∈ Ideal.span ((fun b => monomial b (1 : K)) '' S) ↔ _
  simp only [mem_ideal_span_monomial_image, support_monomial, one_ne_zero,
    ↓reduceIte, Finset.mem_singleton, forall_eq]

def ExponentSaturated (S : Set (Fin (n + 1) →₀ ℕ)) : Prop :=
  ∀ a : Fin (n + 1) →₀ ℕ,
    (∃ m : ℕ, ∀ b : Fin (n + 1) →₀ ℕ, b.degree = m → ∃ c ∈ S, c ≤ b + a) →
      ∃ c ∈ S, c ≤ a

theorem isSaturated_monomialSpan_iff (S : Set (Fin (n + 1) →₀ ℕ)) :
    Hilbert.Polynomial.GradedHilbert.IsSaturated (Hilbert.MonomialBasis.GradedHilbert.monomialSpan K S).toIdeal ↔ ExponentSaturated S := by
  classical
  let I := (Hilbert.MonomialBasis.GradedHilbert.monomialSpan K S).toIdeal
  have hMon : SaturatedMonomialIdeals.GradedHilbert.IsMonomial I := ⟨S, rfl⟩
  constructor
  · intro hSat a ha
    apply (monomial_mem_monomialSpan_iff (K := K) S a).mp
    apply hSat (monomial a (1 : K)) a.degree (isHomogeneous_monomial _ rfl)
    obtain ⟨m, hm⟩ := ha
    refine ⟨m, fun g hg => ?_⟩
    rw [← g.support_sum_monomial_coeff, Finset.sum_mul]
    apply I.sum_mem
    intro b hb
    rw [monomial_mul_monomial, mul_one]
    have hba : monomial (b + a) (1 : K) ∈ I :=
      (monomial_mem_monomialSpan_iff (K := K) S (b + a)).mpr
        (hm b ((Hilbert.MonomialBasis.GradedHilbert.mem_degreeSpace_iff_support g m).mp hg b hb))
    simpa only [C_mul_monomial, mul_one] using I.mul_mem_left (C (g.coeff b)) hba
  · intro hExp f _ _ hmul
    apply (hMon.mem_iff_support f).mpr
    intro a ha
    apply (monomial_mem_monomialSpan_iff (K := K) S a).mpr
    apply hExp a
    obtain ⟨m, hm⟩ := hmul
    refine ⟨m, fun b hb => ?_⟩
    apply (monomial_mem_monomialSpan_iff (K := K) S (b + a)).mp
    apply (hMon.mem_iff_support (monomial b (1 : K) * f)).mp
      (hm (monomial b (1 : K)) (isHomogeneous_monomial _ hb)) (b + a)
    rw [mem_support_iff, coeff_monomial_mul, one_mul]
    exact mem_support_iff.mp ha

theorem isSaturated_monomialSpan_field_independent
    (L : Type v) [Field L] (S : Set (Fin (n + 1) →₀ ℕ)) :
    Hilbert.Polynomial.GradedHilbert.IsSaturated (Hilbert.MonomialBasis.GradedHilbert.monomialSpan K S).toIdeal ↔ Hilbert.Polynomial.GradedHilbert.IsSaturated (Hilbert.MonomialBasis.GradedHilbert.monomialSpan L S).toIdeal := by
  rw [isSaturated_monomialSpan_iff, isSaturated_monomialSpan_iff]

theorem monomialSpan_eq_iff (S T : Set (Fin (n + 1) →₀ ℕ)) :
    (Hilbert.MonomialBasis.GradedHilbert.monomialSpan K S).toIdeal = (Hilbert.MonomialBasis.GradedHilbert.monomialSpan K T).toIdeal ↔
      ∀ a : Fin (n + 1) →₀ ℕ, (∃ b ∈ S, b ≤ a) ↔ ∃ b ∈ T, b ≤ a := by
  constructor
  · intro h a
    rw [← monomial_mem_monomialSpan_iff (K := K),
      ← monomial_mem_monomialSpan_iff (K := K), h]
  · intro h
    apply Ideal.ext
    intro f
    change f ∈ Ideal.span ((fun a => monomial a (1 : K)) '' S) ↔
      f ∈ Ideal.span ((fun a => monomial a (1 : K)) '' T)
    simp only [mem_ideal_span_monomial_image, h]

theorem monomialSpan_eq_field_independent (L : Type v) [Field L]
    (S T : Set (Fin (n + 1) →₀ ℕ)) :
    (Hilbert.MonomialBasis.GradedHilbert.monomialSpan K S).toIdeal = (Hilbert.MonomialBasis.GradedHilbert.monomialSpan K T).toIdeal ↔
      (Hilbert.MonomialBasis.GradedHilbert.monomialSpan L S).toIdeal = (Hilbert.MonomialBasis.GradedHilbert.monomialSpan L T).toIdeal := by
  rw [monomialSpan_eq_iff, monomialSpan_eq_iff]

/-- The monomial generator bound is uniform over all coefficient fields
of the chosen universe, including fields of different characteristics. -/
theorem exists_field_independent_monomial_degree_bound (n : ℕ) (P : Polynomial ℚ) :
    ∃ N : ℕ, ∀ (K : Type u) [Field K] (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)),
      SaturatedMonomialIdeals.GradedHilbert.IsMonomial I.toIdeal → Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal → Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P →
      ∃ G : Finset (Fin (n + 1) →₀ ℕ),
        I.toIdeal = Ideal.span ((fun a => monomial a (1 : K)) ''
          (G : Set (Fin (n + 1) →₀ ℕ))) ∧ ∀ a ∈ G, a.degree ≤ N := by
  obtain ⟨N, hN⟩ := SaturatedMonomialIdeals.GradedHilbert.exists_uniform_saturated_monomial_degree_bound (K := ℚ) n P
  refine ⟨N, fun K _ I hMon hSat hP => ?_⟩
  obtain ⟨S, hS⟩ := hMon
  have hSatS : Hilbert.Polynomial.GradedHilbert.IsSaturated (Hilbert.MonomialBasis.GradedHilbert.monomialSpan K S).toIdeal := by
    change Hilbert.Polynomial.GradedHilbert.IsSaturated (Ideal.span ((fun a => monomial a (1 : K)) '' S))
    rw [← hS]
    exact hSat
  have hPS : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Hilbert.MonomialBasis.GradedHilbert.monomialSpan K S).toIdeal P := by
    change Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Ideal.span ((fun a => monomial a (1 : K)) '' S)) P
    rw [← hS]
    exact hP
  have hSatQ : Hilbert.Polynomial.GradedHilbert.IsSaturated (Hilbert.MonomialBasis.GradedHilbert.monomialSpan ℚ S).toIdeal :=
    (isSaturated_monomialSpan_field_independent (K := K) ℚ S).mp hSatS
  have hPQ : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Hilbert.MonomialBasis.GradedHilbert.monomialSpan ℚ S).toIdeal P :=
    (Hilbert.MonomialBasis.GradedHilbert.hasHilbertPolynomial_monomialSpan_field_independent (K := K) ℚ S P).mp hPS
  obtain ⟨G, hG, hdeg⟩ := hN (Hilbert.MonomialBasis.GradedHilbert.monomialSpan ℚ S) ⟨S, rfl⟩ hSatQ hPQ
  refine ⟨G, hS.trans ?_, hdeg⟩
  exact (monomialSpan_eq_field_independent (K := ℚ) K S
    (G : Set (Fin (n + 1) →₀ ℕ))).mp hG

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.MonomialBound.GradedHilbert
