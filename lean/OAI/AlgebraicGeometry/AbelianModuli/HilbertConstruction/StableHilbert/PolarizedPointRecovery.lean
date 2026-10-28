import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.SaturatedRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PointRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffinePrescribedPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TorsionConfigurationFamilyRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.EmbeddedGroupGraphBounds
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PowerEmbeddingCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.GlobalGraphPowerParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GraphPowerBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationSectionRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.MarkedPointRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PointRecoveryFromEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizedSaturatedRecovery

/-! # Polarized Point Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizedPointRecovery.StableHilbertPolarization

noncomputable section

/-! A normalized uniform graph embedding of an original polarized
family gives a point of the actual stable polarization chart. The
construction retains the saturated Hilbert family and every ordered
level section through the native Hilbert and polarization classifiers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [IsNoetherianRing R]
    (C : CommRingCat) [IsNoetherianRing C]
    {g N : ℕ} {δ : Fin g → ℕ} [NeZero N]
    {f : Spec C ⟶ Spec (.of R)}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec C))
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom)
    (hE : E.degree = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
    (i : Fin (N ^ (2 * g)))
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex (E.dimension + 1) (N ^ (2 * g)))
    (x : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j)
    (H : Polynomial ℚ) (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal C E.dimension H)
    (e : A.abelian.scheme ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal)
    (eL : ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I.ideal 1).pullback e.hom.left).sheaf ≅
      (A.graphBundle.tensorPower (2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ)).sheaf)
    (he : (e.hom.left ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal) ≫
      AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec C)) E.dimension = E.projectivePresentation.embedding.left)
    (hg : 0 < g) (hδ : ∀ k, 0 < δ k) (hN : 3 ≤ N)
    (hunit : IsUnit (N : Γ(Spec C, ⊤)))
    (D : ℕ) (hD : 0 < D) (hdegree : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} E.dimension H ≤ D)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} E.dimension D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} E.dimension D H) H)
    (hlarge : Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ D < N ^ 2)
    (hpoints : ∀ c : ULift (Fin (N ^ (2 * g))),
      (A.abelian.fullLevelGlobalSection A.level (Local.TorsionStableRankLift.liftedFullLevelLabelEnumeration c) ≫ e.hom.left) ≫
        HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal =
          AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap C C (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j C x c)
            (j.coordinate c.down) (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors_selected R i j C x c))
    (qR : Spec (.of R) ⟶ Spec (.of ℚ))

include hE eL he hg hN hunit hD hdegree hlarge hpoints in
theorem exists_of_uniformEmbedding :
    ∃ z : Over.mk f ⟶ PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g
      (Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
      N PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration qR (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
      (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) δ hδ,
      Nonempty (Moduli.Isomorphisms.LevelPreservingIso A
        ((PolarizationParameter.StableHilbertPolarization.universalFamily R i j D H hH g
          (Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
          N PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration qR (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
          (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) δ hδ).pullback z.left)) := by
  obtain ⟨c, hc, _⟩ := Noetherian.TorsionConfigurationLift.noetherianAuxiliaryTorsionConfiguration_unique_hilbertLift
    R C i j x A I e eL hg hδ hN hunit A.level D hD hdegree hlarge hpoints
  have hI := TorsionConfigurationFamilyRecovery.noetherianAuxiliaryTorsionConfiguration_hilbertFamily_recovery
    R C i j x A I e eL hg hδ hN hunit A.level D hD hdegree hlarge hpoints c hc
  exact PolarizedSaturatedRecovery.StableHilbertPolarization.exists_of_saturatedFiber R C A E hE i j D H hH x c hc I hI e he hpoints
    hg hδ hN hunit qR

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizedPointRecovery.StableHilbertPolarization
