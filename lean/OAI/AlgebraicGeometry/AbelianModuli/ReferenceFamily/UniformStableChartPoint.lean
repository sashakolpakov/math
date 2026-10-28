import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.Fine
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizedPointRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.SaturatedEmbeddingCoverage

/-! # Uniform Stable Chart Point -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniformStableChartPoint

noncomputable section

/-! A normalized uniform embedding gives a point on an original stable
polarization chart of the fixed uniform dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (g : ℕ) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) (D : ℕ)
variable (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1) D
    (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1) D
      (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ)) (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ))
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1)
      (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) ≤ D)

include hN hD in
theorem uniformStableChartPoint_of_normalized
    (hg : 0 < g) (hDpos : 0 < D)
    (hlarge : HilbertConstruction.Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ D < N ^ 2)
    (C : CommRingCat) [IsNoetherianRing C] (f : Spec C ⟶ Spec (.of ℚ))
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec C))
    (E : HilbertConstruction.StableHilbert.NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding ℚ (Over.mk f) A
      (HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration.symm 1)) :
    ∃ j : HilbertConstruction.Stable.BalancedFrameIndex.StableBalancedFrameIndex (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1 + 1) (N ^ (2 * g)),
      ∃ z : Over.mk f ⟶ HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.parameter ℚ
        (HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration.symm 1) j D (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) hH
        g (HilbertConstruction.Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (HilbertConstruction.Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
        N HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (𝟙 _) (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
        (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) δ hδ,
        Nonempty (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A
          ((HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.universalFamily ℚ (HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration.symm 1) j D
            (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) hH g
            (HilbertConstruction.Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (HilbertConstruction.Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
            N HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (𝟙 _) (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
            (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) δ hδ).pullback z.left)) := by
  have hunit : IsUnit (N : Γ(Spec C, ⊤)) :=
    Pure.Fine.positive_integer_unit_on_field_base f N (lt_of_lt_of_le (by decide : 0 < 3) hN)
  have hdim : E.embedding.dimension = HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1 := E.dimension_eq
  have hH' : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} E.embedding.dimension D
      (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} E.embedding.dimension D (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ))
        (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) :=
    (congrArg (fun k : ℕ => HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} k D
      (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} k D (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ))
        (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ)) hdim).mpr hH
  have hD' : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} E.embedding.dimension
      (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) ≤ D :=
    (congrArg (fun k : ℕ => HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} k
      (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) ≤ D) hdim).mpr hD
  obtain ⟨z, hz⟩ := HilbertConstruction.StableHilbert.PolarizedPointRecovery.StableHilbertPolarization.exists_of_uniformEmbedding
    ℚ C A E.embedding E.degree_eq (HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration.symm 1) E.chartIndex E.chartPoint
    (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ)
    (E.saturatedIdeal ℚ hg hN hunit) (E.homogeneousIso ℚ hg hN hunit)
    (E.homogeneousTwistingIso ℚ hg hN hunit) (E.homogeneous_embedding ℚ hg hN hunit)
    hg hδ hN hunit D hDpos hD' hH' hlarge
    (fun c => E.homogeneous_markedPoint ℚ hg hN hunit c.down) (𝟙 _)
  let HasChartPoint (k : ℕ) : Prop :=
    ∃ hK : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} k D
        (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} k D (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ))
        (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ),
      ∃ j : HilbertConstruction.Stable.BalancedFrameIndex.StableBalancedFrameIndex (k + 1) (N ^ (2 * g)),
      ∃ z : Over.mk f ⟶ HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.parameter ℚ
        (HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration.symm 1) j D (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) hK
        g (HilbertConstruction.Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (HilbertConstruction.Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
        N HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (𝟙 _) (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
        (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) δ hδ,
        Nonempty (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A
          ((HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.universalFamily ℚ (HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration.symm 1) j D
            (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) hK g
            (HilbertConstruction.Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (HilbertConstruction.Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
            N HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (𝟙 _) (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
            (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) δ hδ).pullback z.left))
  have hlocal : HasChartPoint E.embedding.dimension := ⟨hH', E.chartIndex, z, hz⟩
  have hcanonical : HasChartPoint (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1) :=
    (congrArg HasChartPoint hdim).mp hlocal
  obtain ⟨hK, j, z, hz⟩ := hcanonical
  exact ⟨j, z, hz⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniformStableChartPoint
