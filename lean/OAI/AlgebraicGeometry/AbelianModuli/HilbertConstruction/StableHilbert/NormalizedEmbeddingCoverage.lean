import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.EmbeddingCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EmbeddingSourceTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.GlobalSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.LabelEnumeration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics

/-! # Normalized Embedding Coverage -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NormalizedEmbeddingCoverage.StableHilbertCoverage

noncomputable section

/-! Data for a complete uniform graph embedding whose actual ordered
level sections are the prescribed points of a stable frame chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable {S : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ} [NeZero N]

def indexedLevelSection (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)
    (z : Fin (N ^ (2 * g))) : Over.mk (𝟙 S) ⟶ A.abelian.scheme :=
  (A.level.hom.app (.op (Over.mk (𝟙 S)))
    (LocallyConstant.const S (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration z))).val

variable (R : Type u) [CommRing R] (B : Over (Spec (.of R)))

structure NormalizedGraphEmbedding
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N B.left) (i : Fin (N ^ (2 * g))) where
  embedding : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom
  degree_eq : embedding.degree = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ
  dimension_eq : embedding.dimension = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1
  complete : embedding.HasCompleteSections
  chartIndex : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (embedding.dimension + 1) (N ^ (2 * g))
  chartPoint : B ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i chartIndex
  marked : ∀ z, indexedLevelSection A z ≫ embedding.projectivePresentation.embedding =
    Balanced.FrameChartProjectivePoints.balancedFrameChartProjectivePoint R i chartIndex.frame chartIndex.additional
      chartIndex.coordinate chartIndex.exponent chartIndex.complement chartIndex.balanced
      chartIndex.complete B.left
      (chartPoint.left.appTop.hom.comp
        (Scheme.ΓSpecIso (.of (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i chartIndex.exponent
          chartIndex.balanced))).inv.hom) z

def NormalizedGraphEmbedding.ofLevelIso
    {A A' : PolarizationData.PolarizedAbelianWithFullLevel g δ N B.left}
    {i : Fin (N ^ (2 * g))} (D : NormalizedGraphEmbedding R B A' i)
    (e : Moduli.Isomorphisms.LevelPreservingIso A A') : NormalizedGraphEmbedding R B A i where
  embedding := e.graphPowerEmbedding D.embedding
  degree_eq := D.degree_eq
  dimension_eq := D.dimension_eq
  complete := Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.HasCompleteSections.ofSourceIso D.embedding
    e.abelian e.graphBundleIso D.complete
  chartIndex := D.chartIndex
  chartPoint := D.chartPoint
  marked z := by
    have he : e.abelian.hom ≫ D.embedding.projectivePresentation.embedding =
        (e.graphPowerEmbedding D.embedding).projectivePresentation.embedding :=
      Section.ProjectivePrecomposition.sectionProjectiveMorphism_precomp e.abelian.hom D.embedding.power
        D.embedding.sections D.embedding.covers
        (Section.ChartArbitraryPullback.lineBundleSections_pullback_covers e.abelian.hom.left D.embedding.power
          D.embedding.sections D.embedding.covers)
    have hz : indexedLevelSection A z ≫ e.abelian.hom = indexedLevelSection A' z :=
      e.level (Over.mk (𝟙 B.left))
        (LocallyConstant.const B.left (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration z))
    exact (congrArg (fun f => indexedLevelSection A z ≫ f) he.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun f => f ≫ D.embedding.projectivePresentation.embedding) hz).trans
          (D.marked z)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NormalizedEmbeddingCoverage.StableHilbertCoverage
