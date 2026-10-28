import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniformStableModel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.NoetherianCoverClassification
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.FineFromNoetherianTests
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LocallyNoetherianCoverage

/-! # Uniform Stable Fine -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniformStableFine

noncomputable section

/-! The actual uniform stable model classifies original families on
locally Noetherian tests by normalized affine embeddings. The proved
Noetherian-model and descent adapters then give its original fine
moduli property on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (g : ℕ) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) (D : ℕ)

variable (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1) D
    (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1) D
      (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ)) (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ))
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} (HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1)
      (HilbertConstruction.Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ) ≤ D)

theorem uniformStableModel_classifies_locallyNoetherian
    (hg : 0 < g) (hDpos : 0 < D)
    (hframe : HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * HilbertConstruction.Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ < N ^ 2)
    (hlarge : HilbertConstruction.Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ D < N ^ 2)
    (T : Over (Spec (.of ℚ))) [IsLocallyNoetherian T.left]
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N T.left) :
    ∃! c : T ⟶ (UniformStableModel.uniformStableModel g δ hδ N hN D hH hD).space,
      Nonempty (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso
        ((UniformStableModel.uniformStableModel g δ hδ N hN D hH hD).universal.pullback c.left) A) := by
  classical
  have hunit : IsUnit (N : Γ(T.left, ⊤)) :=
    Pure.Fine.positive_integer_unit_on_field_base T.hom N (lt_of_lt_of_le (by decide : 0 < 3) hN)
  obtain ⟨C, hC, hE⟩ := HilbertConstruction.StableHilbert.LocallyNoetherianCoverage.StableHilbertCoverage.locallyNoetherian_normalizedAffineCover
    ℚ T A hg hδ hN hunit hframe ((HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)).symm 1)
  have hlocal (j : C.I₀) :
      ∃ c : Over.mk (C.f j ≫ T.hom) ⟶ (UniformStableModel.uniformStableModel g δ hδ N hN D hH hD).space,
        Nonempty (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso
          ((UniformStableModel.uniformStableModel g δ hδ N hN D hH hD).universal.pullback c.left)
          (A.pullback (C.f j))) := by
    let : IsNoetherianRing (C.X j) := hC j
    exact UniformStableModel.uniformStableModel_point_of_normalized g δ hδ N hN D hH hD
      hg hDpos hlarge (C.X j) (C.f j ≫ T.hom) (A.pullback (C.f j)) (hE j).some
  choose localPoint localIso using hlocal
  exact Pure.Fine.PurePolarizedModel.classifies_of_locallyNoetherian_openCover
    (UniformStableModel.uniformStableModel g δ hδ N hN D hH hD)
    (UniformStableModel.uniformStableModel_quasiProjective g δ hδ N hN D hH hD) hN
    (fun _ _ a b e => UniformStableModel.uniformStableModel_points_eq g δ hδ N hN D hH hD hg a b e)
    A C.openCover localPoint (fun j => (localIso j).some)

theorem uniformStableModel_isFine
    (hg : 0 < g) (hDpos : 0 < D)
    (hframe : HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * HilbertConstruction.Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ < N ^ 2)
    (hlarge : HilbertConstruction.Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ D < N ^ 2) :
    (UniformStableModel.uniformStableModel g δ hδ N hN D hH hD).IsFine := by
  apply Pure.Fine.PurePolarizedModel.isFine_of_noetherian_classification
    (UniformStableModel.uniformStableModel g δ hδ N hN D hH hD)
    (UniformStableModel.uniformStableModel_quasiProjective g δ hδ N hN D hH hD) hg hδ hN
  intro T hT A
  let : IsNoetherian T.left := hT
  exact uniformStableModel_classifies_locallyNoetherian g δ hδ N hN D hH hD
    hg hDpos hframe hlarge T A

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniformStableFine
