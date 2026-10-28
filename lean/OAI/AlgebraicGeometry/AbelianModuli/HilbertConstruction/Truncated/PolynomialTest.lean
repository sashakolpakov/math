import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.Fibers
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.GenerationBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.GeneratedPolynomialTest

/-! # Polynomial Test -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated

noncomputable section

/-! Finitely many retained ranks determine the Hilbert polynomial on the generated locus. -/

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.GeneratedPolynomialTest.GradedHilbert

universe u

def PolynomialTest.truncatedHilbertTestBound (n N : ℕ) : ℕ := HilbertScheme.Presentations.Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + n

variable {n B : ℕ} {r : ℕ → ℕ}

theorem GradedClassification.TruncatedGradedQuotientData.generated_hilbertPolynomial_finite_test {K : Type u} [Field K]
    (D : GradedClassification.TruncatedGradedQuotientData K (Fin (n + 1)) B r) (N : ℕ)
    (hN : N ≤ B) (hgen : D.GeneratedFromDegree N)
    (hB : PolynomialTest.truncatedHilbertTestBound n N ≤ B) (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial D.generatedIdeal.toIdeal P ↔
      P.natDegree ≤ n ∧ ∀ i : Fin (n + 1),
        (r (HilbertScheme.Presentations.Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val) : ℚ) =
          P.eval ((HilbertScheme.Presentations.Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val : ℕ) : ℚ) := by
  let g : Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) N → HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing K n :=
    fun i => (D.degreeGenerators ⟨N, Nat.lt_succ_of_le hN⟩ i).val
  have hg : ∀ i, (g i).IsHomogeneous N := fun i =>
    (D.degreeGenerators ⟨N, Nat.lt_succ_of_le hN⟩ i).property
  have hI : D.generatedIdeal = HilbertScheme.Presentations.Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg :=
    HomogeneousIdeal.ext (D.generatedIdeal_span_generators N hN hgen)
  have ht := HilbertScheme.Presentations.GeneratedPolynomialTest.GradedHilbert.homogeneousGenerators_hilbertPolynomial_finite_test g N hg P
  rw [← hI] at ht
  refine ht.trans (and_congr_right fun _ => forall_congr' fun i => ?_)
  have hd : HilbertScheme.Presentations.Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val < B + 1 := by
    change HilbertScheme.Presentations.Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + n ≤ B at hB
    omega
  rw [D.retained_hilbertFunction ⟨_, hd⟩]

theorem GradedClassification.TruncatedGradedQuotientData.fieldFiber_hilbertPolynomial_finite_test {R : Type u} [CommRing R]
    (D : GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B r) (N : ℕ)
    (hN : N ≤ B) (hgen : D.GeneratedFromDegree N)
    (hB : PolynomialTest.truncatedHilbertTestBound n N ≤ B) (P : Polynomial ℚ)
    (K : Type u) [Field K] [Algebra R K] :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) D.generatedIdeal).toIdeal P ↔
      P.natDegree ≤ n ∧ ∀ i : Fin (n + 1),
        (r (HilbertScheme.Presentations.Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val) : ℚ) =
          P.eval ((HilbertScheme.Presentations.Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val : ℕ) : ℚ) := by
  rw [← D.baseChange_generatedIdeal K]
  exact (D.baseChange K).generated_hilbertPolynomial_finite_test N hN
    (D.generatedFromDegree_baseChange (R := CommRingCat.of R) (A := CommRingCat.of K) N hgen) hB P

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated
