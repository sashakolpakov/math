import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PointRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.EmbeddedGroupGraphBounds
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PointRecoveryFromEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.LabelEnumeration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizedLevelRecovery

/-! # Polarized Intrinsic Recovery Left -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizedIntrinsicRecoveryLeft.StableHilbertPolarization

noncomputable section

/-! Native scheme embedding compatibility recovers the original
polarized family on the stable polarization chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_of_nativeEmbedding_left
    (R : Type) [CommRing R] [IsNoetherianRing R]
    {T : Over (Spec (.of R))} {g N : ℕ} {δ : Fin g → ℕ} [NeZero N]
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N T.left)
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom)
    (hE : E.degree = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
    (i : Fin (N ^ (2 * g)))
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex (E.dimension + 1) (N ^ (2 * g)))
    (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} E.dimension D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} E.dimension D H) H)
    (c : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (e : A.abelian.scheme ≅
      (Over.pullback (c ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH).left).obj
        (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) E.dimension H).family.scheme)
    (eL : ((((Intrinsic.Presentation.NativeHilbertAbelianLift.presentation (Spec (.of R)) E.dimension H).baseChange
      (c ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH).left).ampleLineBundle).pullback
        e.hom.left).sheaf ≅ E.projectivePresentation.ampleLineBundle.sheaf)
    (he : e.hom.left ≫ ((Intrinsic.Presentation.NativeHilbertAbelianLift.presentation (Spec (.of R)) E.dimension H).baseChange
      (c ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH).left).embedding.left =
        E.projectivePresentation.embedding.left)
    (hm : ∀ z : Fin (N ^ (2 * g)),
      A.abelian.fullLevelGlobalSection A.level (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration z) ≫ e.hom.left ≫
        ((Intrinsic.Presentation.NativeHilbertAbelianLift.presentation (Spec (.of R)) E.dimension H).baseChange
          (c ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH).left).embedding.left =
            (PrescribedPointCriterion.stableHilbertPrescribedPoint R i j D H c z).left)
    (hg : 0 < g) (hδ : ∀ k, 0 < δ k) (hN : 3 ≤ N)
    (hunit : IsUnit (N : Γ(T.left, ⊤))) (qR : Spec (.of R) ⟶ Spec (.of ℚ)) :
    ∃ z : T ⟶ PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g
      (Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
      N PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration qR (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
      (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) δ hδ,
      Nonempty (Moduli.Isomorphisms.LevelPreservingIso A
        ((PolarizationParameter.StableHilbertPolarization.universalFamily R i j D H hH g
          (Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
          N PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration qR (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
          (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) δ hδ).pullback z.left)) := by
  have hb := A.uniformEmbeddedGroupGraphBounds hg hN hunit E hE
  obtain ⟨u, _, hu⟩ := PointRecovery.StableHilbertAbelianPointRecovery.exists_recovery
    R i j D H hH g (Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ)
      (Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ) N PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration
      c A.abelian A.level E.projectivePresentation e eL hb hm
  exact PolarizedLevelRecovery.StableHilbertPolarization.exists_of_fullLevelRecovery R A E hE i j D H hH hδ qR u
    (hu.change_embedding_left he)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizedIntrinsicRecoveryLeft.StableHilbertPolarization
