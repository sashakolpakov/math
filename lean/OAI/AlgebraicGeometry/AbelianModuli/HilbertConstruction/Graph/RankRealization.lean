import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.DegreeRankProfile

/-! # Rank Realization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The uniform graph Hilbert polynomial has its required rank profile
whenever an actual polarized field fiber exists. The proof uses that
fiber's saturated homogeneous ideal and its proved Hilbert polynomial. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert
universe u

theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphHilbert_rankProfile_realizes
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    (D : ℕ) (hD : HilbertScheme.Presentations.Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1)
      (Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) ≤ D) :
    HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1) D
      (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1) D
        (Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ)) (Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) := by
  let E := A.uniformGraphPowerEmbedding hg hδ hN hNk
  let p := SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom E.sections E.covers
  let : IsClosedImmersion p.left := E.closedImmersion
  have : Flat (Over.mk A.abelian.scheme.hom).hom := inferInstanceAs (Flat A.abelian.scheme.hom)
  have : LocallyOfFinitePresentation (Over.mk A.abelian.scheme.hom).hom :=
    inferInstanceAs (LocallyOfFinitePresentation A.abelian.scheme.hom)
  let F := (Closed.Families.FlatClosedFamily.ofEmbedding p).affineProjectivePullback (𝟙 (Spec (.of K)))
  have hF : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial F.homogeneousIdeal.toIdeal (Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) :=
    A.graphBundle_powerEmbedding_hilbertPolynomial hg hN hNk E K (𝟙 (Spec (.of K)))
  exact HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile_realizes F.homogeneousIdeal F.homogeneousIdeal_saturated
    (Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) hF D hD

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
