import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.LevelRecoveryTransfer
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.LocusPointRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.LabelEnumeration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangedGroupGraph

/-! # Graph Power Level Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerLevelRecovery.StableHilbertGraphPower

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
    (hδ : ∀ k, 0 < δ k) (Φ : GraphPower.LocusPresentation.GraphPowerLocusFactory R g N (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) δ)
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
    ∃ z : T ⟶ GraphPowerParameter.StableHilbertGraphPower.parameter R i j D H hH g
      (Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
      N PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) δ Φ,
      Nonempty (Moduli.Isomorphisms.LevelPreservingIso A
        ((GraphPowerParameter.StableHilbertGraphPower.universalFamily R i j D H hH g
          (Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
          N PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) δ Φ).pullback z.left)) := by
  exact ((GraphPowerParameter.StableHilbertGraphPower.locus R i j D H hH g
    (Base.ChangedGroupGraph.uniformAdditionGraphHilbertPolynomial g δ) (Base.ChangedGroupGraph.uniformInversionGraphHilbertPolynomial g δ)
    N PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) δ Φ).exists_point_recovery_of_fullLevel
      (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) hδ u A E hE
      E.projectivePresentation.embedding hrec rfl (HEq.refl _)).imp (fun _ h => h.2)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerLevelRecovery.StableHilbertGraphPower
