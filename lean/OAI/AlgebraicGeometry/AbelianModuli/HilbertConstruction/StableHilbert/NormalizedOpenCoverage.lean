import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FramedEmbeddingCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.BaseMapCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LocallyNoetherian.EmbeddingCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.MarkedFiberFrames

/-! # Normalized Open Coverage -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NormalizedOpenCoverage.StableHilbertCoverage

noncomputable section

/-! Complete uniform graph embeddings normalize on an actual affine open
cover of every locally Noetherian tame polarized family. -/

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

theorem completeEmbedding_normalizedCover [IsAffine B.left] [IsLocallyNoetherian B.left]
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom)
    (hd : E.degree = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
    (hn : E.dimension = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1)
    (hc : E.HasCompleteSections) :
    ∃ C : Scheme.OpenCover.{u} B.left,
      (∀ j, IsAffine (C.X j)) ∧ (∀ j, IsNoetherianRing Γ(C.X j, ⊤)) ∧
      ∀ j, Nonempty (NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding R (Over.mk (C.f j ≫ B.hom))
        (A.pullback (C.f j)) i) := by
  let : IsNoetherianRing Γ(B.left, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top B.left⟩
  obtain ⟨V, hVa, hVe⟩ := A.exists_markedFiberFrames_affineOpenCover A.level
  have hV (j : V.I₀) : ∃ C : Scheme.OpenCover.{0} (V.X j),
      (∀ k, IsAffine (C.X k)) ∧ (∀ k, IsNoetherianRing Γ(C.X k, ⊤)) ∧
      ∀ k, Nonempty (NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding R (Over.mk (C.f k ≫ (V.f j ≫ B.hom)))
        ((A.pullback (V.f j)).pullback (C.f k)) i) := by
    let : IsAffine (V.X j) := hVa j
    let A' := A.pullback (V.f j)
    let B' : Over (Spec (.of R)) := Over.mk (V.f j ≫ B.hom)
    let : IsAffine B'.left := hVa j
    let : IsLocallyNoetherian B'.left :=
      isLocallyNoetherian_of_isOpenImmersion (V.f j)
    let E' := A.graphPowerEmbeddingBaseChange E (V.f j)
    have hu' : IsUnit (N : Γ(B'.left, ⊤)) := Abelian.Schemes.level_unit_under_base_change (V.f j) N hunit
    have hc' : E'.HasCompleteSections :=
      ⟨A.completeGraphPowerEmbeddingBaseChange E (V.f j) hN hunit hc.some⟩
    exact FramedEmbeddingCoverage.StableHilbertCoverage.framed_uniformEmbedding_normalized_cover R B' A' hg hδ hN hu' hlarge
      E' hd hn hc' (fun k => (hVe j k).some) i
  choose C ha hr hC using hV
  let W := V.bind C
  refine ⟨W, fun j => ha j.1 j.2, fun j => hr j.1 j.2, ?_⟩
  rintro ⟨j, k⟩
  exact ⟨NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding.ofPullbackComp R A (V.f j) ((C j).f k) B.hom (hC j k).some⟩

theorem locallyNoetherian_normalizedCover [IsLocallyNoetherian B.left] :
    ∃ C : Scheme.OpenCover.{u} B.left,
      (∀ j, IsAffine (C.X j)) ∧ (∀ j, IsNoetherianRing Γ(C.X j, ⊤)) ∧
      ∀ j, Nonempty (NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding R (Over.mk (C.f j ≫ B.hom))
        (A.pullback (C.f j)) i) := by
  obtain ⟨V, hVa, _, hVE⟩ :=
    A.exists_locallyNoetherian_completeUniformGraphEmbedding_openCover hg hδ hN hunit
  have hV (j : V.I₀) : ∃ C : Scheme.OpenCover.{u} (V.X j),
      (∀ k, IsAffine (C.X k)) ∧ (∀ k, IsNoetherianRing Γ(C.X k, ⊤)) ∧
      ∀ k, Nonempty (NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding R (Over.mk (C.f k ≫ (V.f j ≫ B.hom)))
        ((A.pullback (V.f j)).pullback (C.f k)) i) := by
    let B' : Over (Spec (.of R)) := Over.mk (V.f j ≫ B.hom)
    let : IsAffine B'.left := hVa j
    let : IsLocallyNoetherian B'.left :=
      isLocallyNoetherian_of_isOpenImmersion (V.f j)
    obtain ⟨E, hd, hn, hc⟩ := hVE j
    exact completeEmbedding_normalizedCover R B' (A.pullback (V.f j))
      hg hδ hN (Abelian.Schemes.level_unit_under_base_change (V.f j) N hunit) hlarge i E hd hn hc
  choose C ha hr hC using hV
  let W := V.bind C
  refine ⟨W, fun j => ha j.1 j.2, fun j => hr j.1 j.2, ?_⟩
  rintro ⟨j, k⟩
  exact ⟨NormalizedEmbeddingCoverage.StableHilbertCoverage.NormalizedGraphEmbedding.ofPullbackComp R A (V.f j) ((C j).f k) B.hom (hC j k).some⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NormalizedOpenCoverage.StableHilbertCoverage
