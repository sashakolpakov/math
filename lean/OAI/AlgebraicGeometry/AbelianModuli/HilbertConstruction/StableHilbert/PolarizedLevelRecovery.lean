import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.LevelRecoveryTransfer
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PointRecoveryFromEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.PointRecoveryFromLevel
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.LabelEnumeration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph

/-! # Polarized Level Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizedLevelRecovery.StableHilbertPolarization

noncomputable section

/-! A recovered original full-level family on the stable chart lifts
to the polarization chart through its original projective embedding. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_of_fullLevelRecovery
    (R : Type) [CommRing R] [IsNoetherianRing R]
    {T : Over (Spec (.of R))} {g N : ℕ} {δ : Fin g → ℕ} [NeZero N]
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N T.left)
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom)
    (hE : E.degree = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
    (i : Fin (N ^ (2 * g)))
    (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex (E.dimension + 1) (N ^ (2 * g)))
    (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} E.dimension D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} E.dimension D H) H)
    (hδ : ∀ k, 0 < δ k) (qR : Spec (.of R) ⟶ Spec (.of ℚ))
    (u : T ⟶ LevelParameter.StableHilbertLevel.parameter R i j D H hH g
      (Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
      N PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration)
    (hrec : Embedded.LevelIso.EmbeddedFullLevelRecovery A.abelian A.level
      ((LevelParameter.StableHilbertLevel.family R i j D H hH g
        (Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
        N PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration).pullback u.left)
      E.projectivePresentation.embedding
      (Embedded.LevelIso.abelianProjectiveBaseChangeEmbedding
        (LevelParameter.StableHilbertLevel.family R i j D H hH g
          (Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
          N PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration).abelian
        (LevelParameter.StableHilbertLevel.presentation R i j D H hH g
          (Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
          N PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration) u.left)) :
    ∃ z : T ⟶ PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g
      (Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
      N PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration qR (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
      (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) δ hδ,
      Nonempty (Moduli.Isomorphisms.LevelPreservingIso A
        ((PolarizationParameter.StableHilbertPolarization.universalFamily R i j D H hH g
          (Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
          N PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration qR (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
          (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) δ hδ).pullback z.left)) := by
  let M := LevelParameter.StableHilbertLevel.parameter R i j D H hH g
    (Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
    N PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration
  let F := LevelParameter.StableHilbertLevel.family R i j D H hH g
    (Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
    N PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration
  let P := LevelParameter.StableHilbertLevel.presentation R i j D H hH g
    (Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
    N PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration
  exact (GraphPower.PointRecoveryFromLevel.RationalGlobalGraphPowerLocus.exists_point_recovery_of_fullLevel
    M F P (M.hom ≫ qR) (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
      (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) δ hδ u A E hE
      E.projectivePresentation.embedding hrec rfl (HEq.refl _)).imp (fun _ h => h.2)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizedLevelRecovery.StableHilbertPolarization
