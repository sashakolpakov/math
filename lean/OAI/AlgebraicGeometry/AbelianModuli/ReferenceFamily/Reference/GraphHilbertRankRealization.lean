import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.PELObject
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.RankRealization

/-! # Graph Hilbert Rank Realization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.GraphHilbertRankRealization

noncomputable section

/-! The original admissible PEL datum supplies a genuine complex
polarized fiber. Its uniform graph embedding verifies the rank profile
needed by the fixed Hilbert charts in the ReferenceFamily construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem referenceUniformGraphHilbert_rankProfile
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s) (hP : P.IsAdmissible) (hs : 0 < s)
    (D : ℕ) (hD : HilbertScheme.Presentations.Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{0}
      (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank (3 * s) P.polarizationType - 1)
      (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial (3 * s) P.polarizationType) ≤ D) :
    HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank (3 * s) P.polarizationType - 1) D
      (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0}
        (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank (3 * s) P.polarizationType - 1) D
        (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial (3 * s) P.polarizationType))
      (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial (3 * s) P.polarizationType) := by
  let A := (P.referencePELObject hP (P.referenceOrigin hP) P.μ (RingHom.id ℂ)
    (by ext x; rfl) 3).polarized
  have hδ : ∀ i, 0 < P.polarizationType i := by
    rcases hP with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hpos, _⟩
    exact hpos
  exact A.uniformGraphHilbert_rankProfile_realizes
    (Nat.mul_pos (by decide) hs) hδ (by decide) (by norm_num) D hD

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.GraphHilbertRankRealization
