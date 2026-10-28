import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NormalizedOpenCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.BaseChangeCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.SaturatedEmbeddingCoverage

/-! # Locally Noetherian Coverage -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LocallyNoetherianCoverage.StableHilbertCoverage

noncomputable section

/-! Original locally Noetherian polarized families admit an affine
cover by complete uniform embeddings normalized in actual stable
configuration charts, with their saturated Hilbert models. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

variable (R : Type u) [CommRing R] (B : Over (Spec (.of R)))
variable {g N : ℕ} {δ : Fin g → ℕ} [NeZero N]
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N B.left)
variable (hg : 0 < g) (hδ : ∀ k, 0 < δ k) (hN : 3 ≤ N)
variable (hunit : IsUnit (N : Γ(B.left, ⊤)))
variable (hlarge : Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ < N ^ 2)
variable (i : Fin (N ^ (2 * g)))

include hg hδ hN hunit hlarge

theorem locallyNoetherian_normalizedAffineCover [IsLocallyNoetherian B.left] :
    ∃ C : Scheme.AffineOpenCover.{u} B.left,
      (∀ j, IsNoetherianRing (C.X j)) ∧
      ∀ j, Nonempty (NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding R (Over.mk (C.f j ≫ B.hom))
        (A.pullback (C.f j)) i) := by
  obtain ⟨V, hVa, hVr, hV⟩ := NormalizedOpenCoverage.StableHilbertCoverage.locallyNoetherian_normalizedCover R B A hg hδ hN hunit hlarge i
  let C := V.affineRefinement
  refine ⟨C, fun j => isLocallyNoetherian_Spec.mp (isLocallyNoetherian_of_isOpenImmersion (C.f j)), ?_⟩
  rintro ⟨j, k⟩
  let : IsAffine (V.X j) := hVa j
  let : IsNoetherianRing Γ(V.X j, ⊤) := hVr j
  let B' : Over (Spec (.of R)) := Over.mk (V.f j ≫ B.hom)
  let : IsAffine B'.left := hVa j
  let : IsNoetherianRing Γ(B'.left, ⊤) := hVr j
  let q := (V.X j).affineOpenCover.f k
  let T : Over (Spec (.of R)) := Over.mk ((q ≫ V.f j) ≫ B.hom)
  let : IsAffine T.left :=
    inferInstanceAs (IsAffine (Spec ((V.X j).affineOpenCover.X k)))
  let f : T ⟶ B' := Over.homMk q (Category.assoc q (V.f j) B.hom).symm
  let D := NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding.pullback R (hV j).some f hN
    (Abelian.Schemes.level_unit_under_base_change (V.f j) N hunit)
  exact ⟨NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding.ofLevelIso R T D (Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A (V.f j) q).symm⟩

theorem locallyNoetherian_saturatedNormalizedAffineCover [IsLocallyNoetherian B.left] :
    ∃ C : Scheme.AffineOpenCover.{u} B.left,
      (∀ j, IsNoetherianRing (C.X j)) ∧
      ∀ j, ∃ D : NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding R (Over.mk (C.f j ≫ B.hom)) (A.pullback (C.f j)) i,
        ∃ I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal (C.X j) D.embedding.dimension (Uniform.GeometricGraphEmbedding.uniformGraphEmbeddingHilbertPolynomial g δ),
        ∃ e : (A.pullback (C.f j)).abelian.scheme ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal,
        ∃ _eL : ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I.ideal 1).pullback e.hom.left).sheaf ≅
          ((A.pullback (C.f j)).graphBundle.tensorPower (2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ)).sheaf,
          ((e.hom.left ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal) ≫
            AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (C.X j))) D.embedding.dimension) =
              D.embedding.projectivePresentation.embedding.left ∧
          ∀ c : ULift.{u} (Fin (N ^ (2 * g))),
            ((A.pullback (C.f j)).abelian.fullLevelGlobalSection (A.pullback (C.f j)).level
              (PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration c.down) ≫ e.hom.left) ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal =
                AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (C.X j) (C.X j)
                  (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i D.chartIndex (C.X j) D.chartPoint c)
                  (D.chartIndex.coordinate c.down)
                  (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors_selected R i D.chartIndex (C.X j) D.chartPoint c) := by
  obtain ⟨C, hC, hD⟩ := locallyNoetherian_normalizedAffineCover R B A hg hδ hN hunit hlarge i
  refine ⟨C, hC, fun j => ?_⟩
  let D := (hD j).some
  have hu := Abelian.Schemes.level_unit_under_base_change (C.f j) N hunit
  exact ⟨D, D.saturatedIdeal R hg hN hu, D.homogeneousIso R hg hN hu,
    D.homogeneousTwistingIso R hg hN hu, D.homogeneous_embedding R hg hN hu,
    fun c => D.homogeneous_markedPoint R hg hN hu c.down⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LocallyNoetherianCoverage.StableHilbertCoverage
