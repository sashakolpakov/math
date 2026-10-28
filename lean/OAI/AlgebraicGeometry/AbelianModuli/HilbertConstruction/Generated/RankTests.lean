import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GeneratedCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.PolynomialTest

/-! # Rank Tests -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A finite numerical condition on the prescribed Hilbert polynomial gives the field Hilbert polynomial of every generated parameter point. -/

universe u

theorem Generated.RankTests.generatedHilbertTestDegree_ge (n N : ℕ) : N ≤ HilbertScheme.Presentations.Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N := by
  unfold HilbertScheme.Presentations.Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound HilbertScheme.Presentations.Uniform.GroebnerCompletion.GradedHilbert.homogeneousGroebnerDegreeBound
  have hp : 1 ≤ 2 ^ HilbertScheme.Presentations.ControlledCompletionCertificates.GradedHilbert.polynomialCompletionHorizon n N := Nat.one_le_two_pow
  have hN : N ≤ N * 2 ^ HilbertScheme.Presentations.ControlledCompletionCertificates.GradedHilbert.polynomialCompletionHorizon n N := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left N hp
  exact hN.trans (by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right
      (N * 2 ^ HilbertScheme.Presentations.ControlledCompletionCertificates.GradedHilbert.polynomialCompletionHorizon n N) (Nat.succ_le_succ (Nat.zero_le n)))

def Generated.RankTests.GeneratedHilbertRankTest (n : ℕ) (P : Polynomial ℚ) (N : ℕ) : Prop :=
  P.natDegree ≤ n ∧ ∀ i : Fin (n + 1),
    (((P.eval ((HilbertScheme.Presentations.Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val : ℕ) : ℚ)).num.toNat : ℕ) : ℚ) =
      P.eval ((HilbertScheme.Presentations.Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val : ℕ) : ℚ)

theorem Generated.RankTests.generatedHilbertRanks_finite_test {n N : ℕ} {P : Polynomial ℚ}
    (h : Generated.RankTests.GeneratedHilbertRankTest n P N) (i : Fin (n + 1)) :
    (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N (HilbertScheme.Presentations.Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val) : ℚ) =
      P.eval ((HilbertScheme.Presentations.Bounded.GeneratorFunction.GradedHilbert.generatorHilbertFunctionBound n N + i.val : ℕ) : ℚ) := by
  rw [Uniform.GeneratedCoordinates.generatedHilbertRanks, ite_eq_right (Nat.not_lt.mpr
    ((Generated.RankTests.generatedHilbertTestDegree_ge n N).trans (Nat.le_add_right _ _)))]
  exact h.2 i

variable {R : Type u} [CommRing R] {n B N : ℕ} {P : Polynomial ℚ}
variable (D : Truncated.GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B (Uniform.GeneratedCoordinates.generatedHilbertRanks n P N))

theorem Truncated.GradedClassification.TruncatedGradedQuotientData.generated_fieldHilbertPolynomial (hgen : D.GeneratedFromDegree N)
    (hN : N ≤ B) (hB : Truncated.PolynomialTest.truncatedHilbertTestBound n N ≤ B) (hr : Generated.RankTests.GeneratedHilbertRankTest n P N)
    (K : Type u) [Field K] [Algebra R K] :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) D.generatedIdeal).toIdeal P :=
  (D.fieldFiber_hilbertPolynomial_finite_test N hN hgen hB P K).mpr
    ⟨hr.1, Generated.RankTests.generatedHilbertRanks_finite_test hr⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
