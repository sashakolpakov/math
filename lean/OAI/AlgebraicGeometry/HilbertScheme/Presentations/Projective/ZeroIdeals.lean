import OAI.AlgebraicGeometry.HilbertScheme.Presentations.GroebnerGenerators
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.Localization

/-! # Zero Ideals -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ZeroIdeals.GradedHilbert

noncomputable section

/-! Saturated homogeneous ideals of a projective zero-space over a field are zero or the unit ideal. -/

open _root_.MvPolynomial

universe u

theorem exponent_fin_one (a : Fin 1 →₀ ℕ) : a = Finsupp.single 0 a.degree := by
  apply Finsupp.ext
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [Finsupp.degree_eq_sum]

theorem homogeneous_fin_one_monomial {R : Type u} [CommRing R]
    {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R 0} {d : ℕ} (hf : f.IsHomogeneous d) :
    f = monomial (Finsupp.single 0 d) (f.coeff (Finsupp.single 0 d)) := by
  classical
  apply MvPolynomial.ext
  intro a
  by_cases ha : a = Finsupp.single 0 d
  · subst a
    simp only [coeff_monomial, ↓reduceIte]
  · have hzero : f.coeff a = 0 := by
      by_contra h
      have hd := (Hilbert.MonomialBasis.GradedHilbert.mem_degreeSpace_iff_support f d).mp hf a (mem_support_iff.mpr h)
      exact ha ((exponent_fin_one a).trans (congrArg (Finsupp.single 0) hd))
    rw [hzero, coeff_monomial, ite_eq_right (Ne.symm ha)]

theorem projectiveZero_saturated_ideal_eq_bot_or_top {K : Type u} [Field K]
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K 0)) (hSat : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) :
    I.toIdeal = ⊥ ∨ I.toIdeal = ⊤ := by
  classical
  by_cases hbot : I.toIdeal = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨N, B, hB, hhom⟩ := GroebnerGenerators.GradedHilbert.exists_finite_homogeneous_generators MonomialOrder.lex I
  have hne : B.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.coe_empty, Ideal.span_empty] at hB
    exact hbot hB
  obtain ⟨b, hb⟩ := hne
  obtain ⟨hb0, d, _, hbd⟩ := hhom b hb
  have hbI : b ∈ I.toIdeal := by
    rw [hB]
    exact Ideal.subset_span hb
  have he := homogeneous_fin_one_monomial hbd
  have hc : b.coeff (Finsupp.single 0 d) ≠ 0 := by
    intro hc
    rw [hc, monomial_zero] at he
    exact hb0 he
  have hpow : X (R := K) (0 : Fin 1) ^ d ∈ I.toIdeal := by
    have hbI' : monomial (Finsupp.single 0 d) (b.coeff (Finsupp.single 0 d)) ∈ I.toIdeal := he ▸ hbI
    have hmul := I.toIdeal.mul_mem_left (C (b.coeff (Finsupp.single 0 d))⁻¹) hbI'
    rw [C_mul_monomial, inv_mul_cancel₀ hc, ← X_pow_eq_monomial] at hmul
    exact hmul
  apply Ideal.eq_top_of_isUnit_mem I.toIdeal (x := 1) _ isUnit_one
  apply hSat.mem_of_variable_powers 1 0 (isHomogeneous_one (Fin 1) K)
  intro i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  exact ⟨d, by simpa only [mul_one] using hpow⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ZeroIdeals.GradedHilbert
