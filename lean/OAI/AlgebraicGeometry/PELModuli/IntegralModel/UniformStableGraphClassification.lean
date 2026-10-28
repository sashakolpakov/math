import OAI.AlgebraicGeometry.PELModuli.IntegralModel.UniformStableGraph
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.NoetherianCoverClassification
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FromUnitGraphFactory
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LocallyNoetherianCoverage

/-! # Uniform Stable Graph Classification -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.UniformStableGraphClassification.ReferenceFamily

noncomputable section

/-! The actual stable graph-power model classifies original families
on locally Noetherian tests. Unit-degree locus factories then give the
same original fine-moduli property on arbitrary test schemes. -/

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

theorem uniformStableGraphModel_classifies_locallyNoetherian
    (hNR : IsUnit (N : R)) (hg : 0 < g) (hDpos : 0 < D)
    (hframe : AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * AbelianModuli.HilbertConstruction.Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ < N ^ 2)
    (hlarge : AbelianModuli.HilbertConstruction.Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ D < N ^ 2)
    (T : Over (Spec (.of R))) [IsLocallyNoetherian T.left]
    (A : AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N T.left) :
    ∃! c : T ⟶ (UniformStableGraph.ReferenceFamily.uniformStableGraphModel R g δ hδ N hN D hH hD Φ).space,
      Nonempty (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso
        ((UniformStableGraph.ReferenceFamily.uniformStableGraphModel R g δ hδ N hN D hH hD Φ).universal.pullback c.left) A) := by
  classical
  have hunit : IsUnit (N : Γ(T.left, ⊤)) := by
    simpa only [map_natCast] using hNR.map (AbelianModuli.HilbertConstruction.Coefficient.ModulePresheaf.schemeCoefficientMap T.hom)
  obtain ⟨C, hC, hE⟩ := AbelianModuli.HilbertConstruction.StableHilbert.LocallyNoetherianCoverage.StableHilbertCoverage.locallyNoetherian_normalizedAffineCover
    R T A hg hδ hN hunit hframe ((AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.fullLevelLabelEnumeration (g := g) (n := N)).symm 1)
  have hlocal (j : C.I₀) :
      ∃ c : Over.mk (C.f j ≫ T.hom) ⟶ (UniformStableGraph.ReferenceFamily.uniformStableGraphModel R g δ hδ N hN D hH hD Φ).space,
        Nonempty (AbelianModuli.HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso
          ((UniformStableGraph.ReferenceFamily.uniformStableGraphModel R g δ hδ N hN D hH hD Φ).universal.pullback c.left)
          (A.pullback (C.f j))) := by
    let : IsNoetherianRing (C.X j) := hC j
    exact UniformStableGraph.ReferenceFamily.uniformStableGraphModel_point_of_normalized R g δ hδ N hN D hH hD Φ
      hNR hg hDpos hlarge (C.X j) (C.f j ≫ T.hom) (A.pullback (C.f j)) (hE j).some
  choose localPoint localIso using hlocal
  exact AbelianModuli.ReferenceFamily.Pure.Fine.PurePolarizedModel.classifies_of_locallyNoetherian_openCover
    (UniformStableGraph.ReferenceFamily.uniformStableGraphModel R g δ hδ N hN D hH hD Φ)
    (UniformStableGraph.ReferenceFamily.uniformStableGraphModel_quasiProjective R g δ hδ N hN D hH hD Φ) hN
    (fun _ _ a b e => UniformStableGraph.ReferenceFamily.uniformStableGraphModel_points_eq R g δ hδ N hN D hH hD Φ hNR hg a b e)
    A C.openCover localPoint (fun j => (localIso j).some)

theorem uniformStableGraphModel_isFine
    (hNR : IsUnit (N : R)) (hg : 0 < g) (hDpos : 0 < D)
    (hframe : AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * AbelianModuli.HilbertConstruction.Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ < N ^ 2)
    (hlarge : AbelianModuli.HilbertConstruction.Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ D < N ^ 2)
    (Ψ : ∀ d : ℕ, 0 < d → IsUnit (d : R) → AbelianModuli.HilbertConstruction.GraphPower.LocusPresentation.GraphPowerLocusFactory R g N d δ) :
    (UniformStableGraph.ReferenceFamily.uniformStableGraphModel R g δ hδ N hN D hH hD Φ).IsFine := by
  apply AbelianModuli.ReferenceFamily.Pure.Fine.PurePolarizedModel.isFine_of_unitGraphFactory
    (UniformStableGraph.ReferenceFamily.uniformStableGraphModel R g δ hδ N hN D hH hD Φ)
    (UniformStableGraph.ReferenceFamily.uniformStableGraphModel_quasiProjective R g δ hδ N hN D hH hD Φ)
    hg hδ hN hNR Ψ
  intro T hT A
  let : IsNoetherian T.left := hT
  exact uniformStableGraphModel_classifies_locallyNoetherian R g δ hδ N hN D hH hD Φ
    hNR hg hDpos hframe hlarge T A

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.UniformStableGraphClassification.ReferenceFamily
