import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SyzygyGraphProjection
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SyzygiesFromPolynomialKernel

/-! # Syzygy Substitution Comparison -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.SyzygySubstitutionComparison.GradedHilbert

noncomputable section

/-! The graph elimination kernel agrees with substitution Yᵢ ↦ gᵢt in a polynomial ring over the original coordinates. -/

open _root_.MvPolynomial

variable {K σ ι τ : Type*} [Field K]

def graphOutput (h : ι → MvPolynomial τ K) :
    MvPolynomial (ι ⊕ τ) K →ₐ[K] MvPolynomial τ K := aeval (Sum.elim h X)

theorem graphSubstitution_eq_rename_output (h : ι → MvPolynomial τ K)
    (p : MvPolynomial (ι ⊕ τ) K) :
    GraphSubstitutionIdeal.GradedHilbert.graphSubstitution h p = rename Sum.inr (graphOutput h p) := by
  have he : GraphSubstitutionIdeal.GradedHilbert.graphSubstitution h = (rename Sum.inr).comp (graphOutput h) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i <;> simp [GraphSubstitutionIdeal.GradedHilbert.graphSubstitution, graphOutput]
  exact AlgHom.congr_fun he p

theorem graphSubstitution_eq_zero_iff_output (h : ι → MvPolynomial τ K)
    (p : MvPolynomial (ι ⊕ τ) K) :
    GraphSubstitutionIdeal.GradedHilbert.graphSubstitution h p = 0 ↔ graphOutput h p = 0 := by
  rw [graphSubstitution_eq_rename_output, rename_eq_zero_iff_of_injective _ Sum.inr_injective]

theorem optionEquivLeft_rename_some (p : MvPolynomial σ K) :
    optionEquivLeft K σ (rename some p) = Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, rename_X, optionEquivLeft_X_some]

def syzygyPolynomialSubstitution (g : ι → MvPolynomial σ K) :
    MvPolynomial (ι ⊕ σ) K →ₐ[K] Polynomial (MvPolynomial σ K) :=
  ((Linear.PolynomialCoefficients.GradedHilbert.linearVariableSubstitution g).restrictScalars K).comp (sumAlgEquiv K ι σ).toAlgHom

theorem syzygyPolynomialSubstitution_eq_graph_output
    (g : ι → MvPolynomial σ K) (p : MvPolynomial (ι ⊕ σ) K) :
    syzygyPolynomialSubstitution g p = optionEquivLeft K σ
      (graphOutput (SyzygyGraphEquations.GradedHilbert.syzygyGraphData g) (rename SyzygyGraphProjection.GradedHilbert.syzygyVariableEmbedding p)) := by
  have he : syzygyPolynomialSubstitution g = (optionEquivLeft K σ).toAlgHom.comp
      ((graphOutput (SyzygyGraphEquations.GradedHilbert.syzygyGraphData g)).comp (rename SyzygyGraphProjection.GradedHilbert.syzygyVariableEmbedding)) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | inl i =>
      simp [syzygyPolynomialSubstitution, Linear.PolynomialCoefficients.GradedHilbert.linearVariableSubstitution, SyzygyGraphProjection.GradedHilbert.syzygyVariableEmbedding,
        graphOutput, SyzygyGraphEquations.GradedHilbert.syzygyGraphData, optionEquivLeft_rename_some]
    | inr i =>
      simp [syzygyPolynomialSubstitution, Linear.PolynomialCoefficients.GradedHilbert.linearVariableSubstitution, SyzygyGraphProjection.GradedHilbert.syzygyVariableEmbedding, graphOutput]
  exact AlgHom.congr_fun he p

theorem syzygy_graph_kernel_comparison (g : ι → MvPolynomial σ K)
    (p : MvPolynomial (ι ⊕ σ) K) :
    GraphSubstitutionIdeal.GradedHilbert.graphSubstitution (SyzygyGraphEquations.GradedHilbert.syzygyGraphData g) (rename SyzygyGraphProjection.GradedHilbert.syzygyVariableEmbedding p) = 0 ↔
      Linear.PolynomialCoefficients.GradedHilbert.linearVariableSubstitution g (sumAlgEquiv K ι σ p) = 0 := by
  change _ ↔ syzygyPolynomialSubstitution g p = 0
  rw [syzygyPolynomialSubstitution_eq_graph_output, graphSubstitution_eq_zero_iff_output]
  exact (map_eq_zero_iff (optionEquivLeft K σ) (optionEquivLeft K σ).injective).symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.SyzygySubstitutionComparison.GradedHilbert
