import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PresentationCompleteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Geometric.NormalizedGraphPolynomial
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NormalizedClassCompleteness

/-! # Graph Presentation Completeness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPresentationCompleteness.StableHilbertCoverage

noncomputable section

/-! A standard marked frame and the original normalized graph-power
relation force completeness of the canonical projective sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u

theorem canonicalGraphPresentation_field_rank
    {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.abelian.scheme)
    (h : Line.Bundles.LineBundle.classOf (A.abelian.zeroNormalizedBundle P.ampleLineBundle) =
      Line.Bundles.LineBundle.classOf (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)))
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj
      P.ampleLineBundle.sheaf) = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ := by
  exact (NormalizedClassCompleteness.StableHilbertCoverage.normalizedLineBundle_sections_finrank_eq A.abelian P.ampleLineBundle
    (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)) h).trans
    (A.graphBundle_positivePower_sections_finrank_normalized hg hN hNk
      (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ))

theorem canonicalGraphPresentation_geometricallyComplete
    {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (P : Projective.ProjectivePresentations.ProjectivePresentation A.abelian.scheme)
    (σ : Fin (P.dimension + 1) → Multiplicative (Fin (2 * g) → ZMod N))
    (hσ : ∀ i, Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 S)) A.abelian A.level P (σ i) =
      Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint S P.dimension i)
    (h : Line.Bundles.LineBundle.classOf (A.abelian.zeroNormalizedBundle P.ampleLineBundle) =
      Line.Bundles.LineBundle.classOf (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)))
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N)
    (hunit : IsUnit (N : Γ(S, ⊤)))
    (hn : P.dimension + 1 = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ) :
    ProperFlat.SectionFiberCriterion.GeometricallyCompleteSectionFamily A.abelian.scheme.hom P.ampleLineBundle.sheaf
      P.canonicalSectionData.sections (𝟙 S) := by
  apply PresentationCompleteness.StableHilbertCoverage.canonicalSections_geometricallyComplete_of_markedFrame_rank A.abelian A.level P σ hσ
  intro K _ f
  exact (canonicalGraphPresentation_field_rank (A.pullback f) (P.baseChange f)
    (NormalizedClassCompleteness.StableHilbertCoverage.normalizedGraphPowerClass_baseChange A P h f) hg hδ hN
    (Geometric.NormalizedGraphPolynomial.fieldPoint_natCast_ne_zero_of_global_unit hunit f)).trans hn.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPresentationCompleteness.StableHilbertCoverage
