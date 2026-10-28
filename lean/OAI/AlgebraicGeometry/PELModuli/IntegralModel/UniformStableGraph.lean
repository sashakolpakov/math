import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.Fine
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerInjectivity
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.UniformStableChartPoint

/-! # Uniform Stable Graph -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.UniformStableGraph.ReferenceFamily

noncomputable section

/-! The concrete affine-base pure model at one sufficiently large level.
Its parameter scheme, universal family, projective presentation, and
point uniqueness are the actual glued stable-Hilbert constructions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [IsNoetherianRing R]
    (g : ℕ) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) (D : ℕ)

variable (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} (AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1) D
    (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} (AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1) D
      (AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ)) (AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ))
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} (AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1)
      (AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) ≤ D)

variable (Φ : AbelianModuli.HilbertConstruction.GraphPower.LocusPresentation.GraphPowerLocusFactory R g N (AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) δ)

def uniformStableGraphModel : AbelianModuli.ReferenceFamily.Pure.Fine.PurePolarizedModel g δ N (Spec (.of R)) where
  space := AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerGluing.StableHilbertGraphPowerGluing.parameter R
    ((AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)).symm 1) D
    (AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) hH hD g
    (AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
    N (AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)) (AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) δ Φ
  universal := AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerGluedFamily.StableHilbertGraphPowerGluing.universalFamily R
    ((AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)).symm 1) D
    (AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) hH hD g
    (AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
    N (AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)) (AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) δ Φ (AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) hδ hN

def uniformStableGraphModel_quasiProjective :
    AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation (uniformStableGraphModel R g δ hδ N hN D hH hD Φ).space :=
  AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerGluing.StableHilbertGraphPowerGluing.quasiProjective R
    ((AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)).symm 1) D
    (AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) hH hD g
    (AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
    N (AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)) (AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) δ Φ

theorem uniformStableGraphModel_points_eq (hNR : IsUnit (N : R)) (hg : 0 < g)
    {T : Over (Spec (.of R))} [IsLocallyNoetherian T.left]
    (a b : T ⟶ (uniformStableGraphModel R g δ hδ N hN D hH hD Φ).space)
    (e : AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso
      ((uniformStableGraphModel R g δ hδ N hN D hH hD Φ).universal.pullback a.left)
      ((uniformStableGraphModel R g δ hδ N hN D hH hD Φ).universal.pullback b.left)) : a = b :=
  AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerInjectivity.StableHilbertGraphPowerGluing.points_eq_of_iso R
    ((AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)).symm 1) D
    (AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) hH hD g
    (AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
    N (AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)) (AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) δ Φ (AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) hδ hNR hg hN
    (Nat.sub_add_cancel (Nat.succ_le_of_lt (AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank_pos g δ hδ))) a b e

theorem uniformStableGraphModel_point_of_normalized
    (hNR : IsUnit (N : R))
    (hg : 0 < g) (hDpos : 0 < D)
    (hlarge : AbelianModuli.HilbertConstruction.Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ D < N ^ 2)
    (C : CommRingCat) [IsNoetherianRing C] (f : Spec C ⟶ Spec (.of R))
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec C))
    (E : AbelianModuli.HilbertConstruction.StableHilbert.NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding R (Over.mk f) A
      ((AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)).symm 1)) :
    ∃ c : Over.mk f ⟶ (uniformStableGraphModel R g δ hδ N hN D hH hD Φ).space,
      Nonempty (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso
        ((uniformStableGraphModel R g δ hδ N hN D hH hD Φ).universal.pullback c.left) A) := by
  obtain ⟨j, z, ⟨ez⟩⟩ := UniformStableChartPoint.ReferenceFamily.uniformStableGraphChartPoint_of_normalized
    R g δ hδ N hN D hH hD Φ hNR hg hDpos hlarge C f A E
  let u := AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerGluing.StableHilbertGraphPowerGluing.chartMap R
    ((AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)).symm 1) D
    (AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) hH hD g
    (AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
    N (AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)) (AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) δ Φ j
  refine ⟨z ≫ u, ⟨?_⟩⟩
  exact (ez.trans (AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerGluedFamily.StableHilbertGraphPowerGluing.universalFamily_chartIsoOnTest
    R ((AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)).symm 1) D
    (AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) hH hD g
    (AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
    N (AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)) (AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) δ Φ (AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) hδ hN j z.left)).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.UniformStableGraph.ReferenceFamily
