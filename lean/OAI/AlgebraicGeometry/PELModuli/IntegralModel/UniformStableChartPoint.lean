import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.Fine
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerPointRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.SaturatedEmbeddingCoverage

/-! # Uniform Stable Chart Point -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.UniformStableChartPoint.ReferenceFamily

noncomputable section

/-! A normalized uniform embedding gives a point on an original stable
polarization chart of the fixed uniform dimension. -/

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

include hδ hN hD in
theorem uniformStableGraphChartPoint_of_normalized
    (hNR : IsUnit (N : R))
    (hg : 0 < g) (hDpos : 0 < D)
    (hlarge : AbelianModuli.HilbertConstruction.Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ D < N ^ 2)
    (C : CommRingCat) [IsNoetherianRing C] (f : Spec C ⟶ Spec (.of R))
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec C))
    (E : AbelianModuli.HilbertConstruction.StableHilbert.NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding R (Over.mk f) A
      (AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration.symm 1)) :
    ∃ j : AbelianModuli.HilbertConstruction.Stable.BalancedFrameIndex.StableBalancedFrameIndex (AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1 + 1) (N ^ (2 * g)),
      ∃ z : Over.mk f ⟶ AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower.parameter R
        (AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration.symm 1) j D (AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) hH
        g (AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
        N AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) δ Φ,
        Nonempty (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A
          ((AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower.universalFamily R (AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration.symm 1) j D
            (AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) hH g
            (AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
            N AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) δ Φ).pullback z.left)) := by
  have hunit : IsUnit (N : Γ(Spec C, ⊤)) := by
    simpa only [map_natCast] using hNR.map (AbelianModuli.HilbertConstruction.Coefficient.ModulePresheaf.schemeCoefficientMap f)
  have hdim : E.embedding.dimension = AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1 := E.dimension_eq
  have hH' : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} E.embedding.dimension D
      (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} E.embedding.dimension D (AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ))
        (AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) :=
    (congrArg (fun k : ℕ => HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} k D
      (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} k D (AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ))
        (AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ)) hdim).mpr hH
  have hD' : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} E.embedding.dimension
      (AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) ≤ D :=
    (congrArg (fun k : ℕ => HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} k
      (AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) ≤ D) hdim).mpr hD
  obtain ⟨z, hz⟩ := AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerPointRecovery.StableHilbertGraphPower.exists_of_uniformEmbedding
    R C A E.embedding E.degree_eq (AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration.symm 1) E.chartIndex E.chartPoint
    (AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ)
    (E.saturatedIdeal R hg hN hunit) (E.homogeneousIso R hg hN hunit)
    (E.homogeneousTwistingIso R hg hN hunit) (E.homogeneous_embedding R hg hN hunit)
    hg hδ hN hunit D hDpos hD' hH' hlarge
    (fun c => E.homogeneous_markedPoint R hg hN hunit c.down) Φ
  let HasChartPoint (k : ℕ) : Prop :=
    ∃ hK : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} k D
        (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} k D (AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ))
        (AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ),
      ∃ j : AbelianModuli.HilbertConstruction.Stable.BalancedFrameIndex.StableBalancedFrameIndex (k + 1) (N ^ (2 * g)),
      ∃ z : Over.mk f ⟶ AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower.parameter R
        (AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration.symm 1) j D (AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) hK
        g (AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
        N AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) δ Φ,
        Nonempty (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso A
          ((AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower.universalFamily R (AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration.symm 1) j D
            (AbelianModuli.HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) hK g
            (AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
            N AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) δ Φ).pullback z.left))
  have hlocal : HasChartPoint E.embedding.dimension := ⟨hH', E.chartIndex, z, hz⟩
  have hcanonical : HasChartPoint (AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1) :=
    (congrArg HasChartPoint hdim).mp hlocal
  obtain ⟨hK, j, z, hz⟩ := hcanonical
  exact ⟨j, z, hz⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.UniformStableChartPoint.ReferenceFamily
