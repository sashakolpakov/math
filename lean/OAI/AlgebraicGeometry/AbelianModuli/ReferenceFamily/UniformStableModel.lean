import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.Fine
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationInjectivity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniformStableChartPoint

/-! # Uniform Stable Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniformStableModel

noncomputable section

/-! The concrete rational pure model at one sufficiently large level.
Its parameter scheme, universal family, projective presentation, and
point uniqueness are the actual glued stable-Hilbert constructions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (g : ℕ) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) (D : ℕ)

variable (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1) D
    (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1) D
      (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ)) (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ))
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1)
      (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) ≤ D)

def uniformStableModel : Pure.Fine.PurePolarizedModel g δ N (Spec (.of ℚ)) where
  space := HilbertConstruction.StableHilbert.PolarizationGluing.StableHilbertPolarizationGluing.parameter ℚ
    ((HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)).symm 1) D
    (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) hH hD g
    (HilbertConstruction.Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (HilbertConstruction.Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
    N (HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)) (𝟙 _) (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
    (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) δ hδ
  universal := HilbertConstruction.StableHilbert.GluedPolarizedFamily.StableHilbertPolarizationGluing.universalFamily ℚ
    ((HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)).symm 1) D
    (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) hH hD g
    (HilbertConstruction.Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (HilbertConstruction.Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
    N (HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)) (𝟙 _) (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
    (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) δ hδ hN

def uniformStableModel_quasiProjective :
    HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation (uniformStableModel g δ hδ N hN D hH hD).space :=
  HilbertConstruction.StableHilbert.PolarizationGluing.StableHilbertPolarizationGluing.quasiProjective ℚ
    ((HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)).symm 1) D
    (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) hH hD g
    (HilbertConstruction.Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (HilbertConstruction.Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
    N (HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)) (𝟙 _) (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
    (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) δ hδ

theorem uniformStableModel_points_eq (hg : 0 < g)
    {T : Over (Spec (.of ℚ))} [IsLocallyNoetherian T.left]
    (a b : T ⟶ (uniformStableModel g δ hδ N hN D hH hD).space)
    (e : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso
      ((uniformStableModel g δ hδ N hN D hH hD).universal.pullback a.left)
      ((uniformStableModel g δ hδ N hN D hH hD).universal.pullback b.left)) : a = b :=
  HilbertConstruction.StableHilbert.PolarizationInjectivity.StableHilbertPolarizationGluing.points_eq_of_iso ℚ
    ((HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)).symm 1) D
    (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) hH hD g
    (HilbertConstruction.Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (HilbertConstruction.Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
    N (HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)) (𝟙 _) (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
    (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) δ hδ hg hN rfl
    (Nat.sub_add_cancel (Nat.succ_le_of_lt (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank_pos g δ hδ))) a b e

theorem uniformStableModel_point_of_normalized
    (hg : 0 < g) (hDpos : 0 < D)
    (hlarge : HilbertConstruction.Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ D < N ^ 2)
    (C : CommRingCat) [IsNoetherianRing C] (f : Spec C ⟶ Spec (.of ℚ))
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec C))
    (E : HilbertConstruction.StableHilbert.NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding ℚ (Over.mk f) A
      ((HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)).symm 1)) :
    ∃ c : Over.mk f ⟶ (uniformStableModel g δ hδ N hN D hH hD).space,
      Nonempty (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso
        ((uniformStableModel g δ hδ N hN D hH hD).universal.pullback c.left) A) := by
  obtain ⟨j, z, ⟨ez⟩⟩ := UniformStableChartPoint.uniformStableChartPoint_of_normalized
    g δ hδ N hN D hH hD hg hDpos hlarge C f A E
  let u := HilbertConstruction.StableHilbert.PolarizationGluing.StableHilbertPolarizationGluing.chartMap ℚ
    ((HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)).symm 1) D
    (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) hH hD g
    (HilbertConstruction.Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (HilbertConstruction.Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
    N (HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)) (𝟙 _) (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
    (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) δ hδ j
  refine ⟨z ≫ u, ⟨?_⟩⟩
  exact (ez.trans (HilbertConstruction.StableHilbert.GluedPolarizedFamily.StableHilbertPolarizationGluing.universalFamily_chartIsoOnTest
    ℚ ((HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)).symm 1) D
    (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) hH hD g
    (HilbertConstruction.Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (HilbertConstruction.Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
    N (HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)) (𝟙 _) (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
    (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) δ hδ hN j z.left)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniformStableModel
