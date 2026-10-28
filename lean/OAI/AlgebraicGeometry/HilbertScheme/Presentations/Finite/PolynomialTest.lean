import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Bounded.GeneratorFunction

/-! # Polynomial Test -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.PolynomialTest.GradedHilbert

noncomputable section

/-! For bounded homogeneous generators, the Hilbert-polynomial condition is determined by finitely many actual quotient dimensions. -/

open _root_.MvPolynomial

universe u

theorem monomialHilbertPolynomial_natDegree_le {n : ℕ} (G : Finset (Fin (n + 1) →₀ ℕ)) :
    (Hilbert.Existence.GradedHilbert.monomialHilbertPolynomial G).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro t _
  exact (Polynomial.natDegree_smul_le _ _).trans (Polynomial.natDegree_preHilbertPoly ℚ n _).le

variable {K : Type u} [Field K] {n : ℕ}

theorem hilbertPolynomial_natDegree_le (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n))
    (P : Polynomial ℚ) (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P) : P.natDegree ≤ n := by
  let m : MonomialOrder (Fin (n + 1)) := MonomialOrder.lex
  obtain ⟨G, hG⟩ := (InitialIdeal.GradedHilbert.initialIdeal_isMonomial m I.toIdeal).finite_generators
  have hQ : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal (Hilbert.Existence.GradedHilbert.monomialHilbertPolynomial G) := by
    apply (InitialIdeal.GradedHilbert.hasHilbertPolynomial_initialIdeal_iff m I _).mp
    rw [hG]
    exact Hilbert.Existence.GradedHilbert.monomialSpan_hasHilbertPolynomial G
  rw [Hilbert.Polynomial.GradedHilbert.hilbertPolynomial_unique hP hQ]
  exact monomialHilbertPolynomial_natDegree_le G

theorem bounded_generators_hilbertPolynomial_finite_test
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (B : Finset (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n))
    (hB : I.toIdeal = Ideal.span (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)))
    (D : ℕ) (hb : ∀ b ∈ B, b ≠ 0 ∧ ∃ d ≤ D, b.IsHomogeneous d) (P : Polynomial ℚ) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P ↔
      P.natDegree ≤ n ∧ ∀ i : Fin (n + 1),
        (Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal (Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n D + i.val) : ℚ) =
          P.eval ((Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n D + i.val : ℕ) : ℚ) := by
  constructor
  · intro hP
    refine ⟨hilbertPolynomial_natDegree_le I P hP, fun i => ?_⟩
    exact Bounded.GeneratorFunction.GradedHilbert.bounded_generators_hilbertFunction_eq I B hB D hb P hP _ (Nat.le_add_right _ _)
  · rintro ⟨hdegP, hvals⟩
    obtain ⟨Q, hQ⟩ := Hilbert.Existence.GradedHilbert.exists_hilbertPolynomial I
    have heq : Q = P := by
      apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq Q P
        (f := fun i : Fin (n + 1) => ((Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n D + i.val : ℕ) : ℚ))
      · intro i j hij
        change ((Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n D + i.val : ℕ) : ℚ) =
          ((Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n D + j.val : ℕ) : ℚ) at hij
        have hnat : Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n D + i.val =
            Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n D + j.val := by exact_mod_cast hij
        exact Fin.ext (Nat.add_left_cancel hnat)
      · intro i
        rw [← Bounded.GeneratorFunction.GradedHilbert.bounded_generators_hilbertFunction_eq I B hB D hb Q hQ _ (Nat.le_add_right _ _)]
        exact hvals i
      · rw [Fintype.card_fin]
        exact Nat.lt_succ_of_le (max_le (hilbertPolynomial_natDegree_le I Q hQ) hdegP)
    exact heq ▸ hQ

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.PolynomialTest.GradedHilbert
