import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated.QuotientBaseChange

/-! # Fibers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated

noncomputable section

/-! The prescribed finite Grassmannian ranks recover the retained Hilbert function on every field fiber. -/

universe u v

variable {n B : ℕ} {r : ℕ → ℕ}

theorem GradedClassification.TruncatedGradedQuotientData.retained_hilbertFunction {K : Type u} [Field K]
    (D : GradedClassification.TruncatedGradedQuotientData K (Fin (n + 1)) B r) (d : Fin (B + 1)) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction D.generatedIdeal.toIdeal d = r d := by
  have hr := (D.quotient d).rankAtStalk_eq (⟨⊥, inferInstance⟩ : PrimeSpectrum K)
  rw [Module.rankAtStalk_eq_finrank_of_free] at hr
  change Module.finrank K (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K d ⧸
    Homogeneous.IdealIncidence.homogeneousDegreeRelations D.generatedIdeal d) = r d
  rw [D.generatedIdeal_degree]
  exact hr

theorem GradedClassification.TruncatedGradedQuotientData.fieldFiber_retained_hilbertFunction {R : Type u} [CommRing R]
    (D : GradedClassification.TruncatedGradedQuotientData R (Fin (n + 1)) B r)
    (K : Type v) [Field K] [Algebra R K] (d : Fin (B + 1)) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) D.generatedIdeal).toIdeal d = r d := by
  rw [← D.baseChange_generatedIdeal K]
  exact (D.baseChange K).retained_hilbertFunction d

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Truncated
