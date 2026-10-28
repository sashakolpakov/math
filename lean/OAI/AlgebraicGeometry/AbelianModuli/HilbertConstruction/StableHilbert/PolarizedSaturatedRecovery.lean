import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizedIntrinsicRecoveryLeft
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.SaturatedMarkedRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.TorsionStableRankLift

/-! # Polarized Saturated Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizedSaturatedRecovery.StableHilbertPolarization

noncomputable section

/-! The original saturated fiber and its homogeneous marked sections
supply the native recovery needed by the stable polarization chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [IsNoetherianRing R]
    (C : Type) [CommRing C] [IsNoetherianRing C]
variable {g N : ℕ} {δ : Fin g → ℕ} [NeZero N] {f : Spec (.of C) ⟶ Spec (.of R)}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of C)))
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom)
variable (hE : E.degree = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
variable (i : Fin (N ^ (2 * g)))
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex (E.dimension + 1) (N ^ (2 * g)))
    (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} E.dimension D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} E.dimension D H) H)
variable (x : Over.mk f ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j)
    (c : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (hc : c ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i j D H = x)
variable (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal C E.dimension H)
variable (hI : HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) E.dimension) c
      (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D H) = I.nativeHilbertFamily f)
variable (e : A.abelian.scheme ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal)
    (he : (e.hom.left ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal) ≫
      AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of C))) E.dimension = E.projectivePresentation.embedding.left)
variable (hpoints : ∀ z : ULift (Fin (N ^ (2 * g))),
      (A.abelian.fullLevelGlobalSection A.level (Local.TorsionStableRankLift.liftedFullLevelLabelEnumeration z) ≫ e.hom.left) ≫
        HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal =
          AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of C) C (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j (.of C) x z)
            (j.coordinate z.down) (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors_selected R i j (.of C) x z))
variable (hg : 0 < g) (hδ : ∀ k, 0 < δ k) (hN : 3 ≤ N)
    (hunit : IsUnit (N : Γ(Spec (.of C), ⊤))) (qR : Spec (.of R) ⟶ Spec (.of ℚ))

include hE hc hI he hpoints hg hN hunit in
theorem exists_of_saturatedFiber :
    ∃ z : Over.mk f ⟶ PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g
      (Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
      N PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration qR (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
      (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) δ hδ,
      Nonempty (Moduli.Isomorphisms.LevelPreservingIso A
        ((PolarizationParameter.StableHilbertPolarization.universalFamily R i j D H hH g
          (Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
          N PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration qR (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
          (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) δ hδ).pullback z.left)) := by
  let e₀ := SaturatedRecovery.StableHilbertSaturatedRecovery.sourceIso R i j D H hH c I hI e
  let P₀ := Intrinsic.Presentation.NativeHilbertAbelianLift.presentation (Spec (.of R)) E.dimension H
  let b := c ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH
  have he₀ : e₀.hom.left ≫ (P₀.baseChange b.left).embedding.left =
      E.projectivePresentation.embedding.left :=
    SaturatedRecovery.StableHilbertSaturatedRecovery.sourceIso_embedding_left R i j D H hH c I hI e
      E.projectivePresentation.embedding he
  let eL₀ := SaturatedRecovery.StableHilbertSaturatedRecovery.sourceTwistingIso R i j D H hH c I hI e
    E.projectivePresentation.embedding he
  have hm (z : Fin (N ^ (2 * g))) :
      A.abelian.fullLevelGlobalSection A.level (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration z) ≫ e₀.hom.left ≫
        (P₀.baseChange b.left).embedding.left = (PrescribedPointCriterion.stableHilbertPrescribedPoint R i j D H c z).left :=
    SaturatedMarkedRecovery.StableHilbertSaturatedRecovery.sourceIso_markedPoint R i j D H hH c x hc I hI e
      E.projectivePresentation.embedding he z
      (A.abelian.fullLevelGlobalSection A.level (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration z)) (hpoints ⟨z⟩)
  exact PolarizedIntrinsicRecoveryLeft.StableHilbertPolarization.exists_of_nativeEmbedding_left (T := Over.mk f) R A E hE i j D H hH c e₀ eL₀ he₀ hm
    hg hδ hN hunit qR

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizedSaturatedRecovery.StableHilbertPolarization
