import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Existence

/-! # Hilbert Polynomial Degree Bound -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.HilbertPolynomialDegreeBound

noncomputable section

/-! The homogeneous coordinate Hilbert polynomial has degree bounded by the ambient dimension. -/

open _root_.MvPolynomial OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert
universe u

theorem monomialHilbertPolynomial_natDegree_le {r : ℕ}
    (G : Finset (Fin (r + 1) →₀ ℕ)) : (HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert.monomialHilbertPolynomial G).natDegree ≤ r := by
  classical
  unfold HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert.monomialHilbertPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro t _
  exact (Polynomial.natDegree_smul_le _ _).trans
    (Polynomial.natDegree_preHilbertPoly ℚ r (t.sup id).degree).le

theorem exists_hilbertPolynomial_natDegree_le {K : Type u} [Field K] {r : ℕ}
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading K r)) :
    ∃ P : Polynomial ℚ, HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P ∧ P.natDegree ≤ r := by
  let m : MonomialOrder (Fin (r + 1)) := MonomialOrder.lex
  obtain ⟨G, hG⟩ := (HilbertScheme.Presentations.InitialIdeal.GradedHilbert.initialIdeal_isMonomial m I.toIdeal).finite_generators
  refine ⟨HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert.monomialHilbertPolynomial G, ?_, monomialHilbertPolynomial_natDegree_le G⟩
  apply (HilbertScheme.Presentations.InitialIdeal.GradedHilbert.hasHilbertPolynomial_initialIdeal_iff m I _).mp
  rw [hG]
  exact HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert.monomialSpan_hasHilbertPolynomial G

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.HilbertPolynomialDegreeBound
