import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.UniformGraphEmbeddingCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EmbeddingSourceTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.PointEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Moduli.Coherence

/-! # Embedding Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Complete uniform graph embeddings exist on an affine open cover of
every locally Noetherian tame polarized family; composition recovery
retains the complete coefficient-section basis. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.exists_locallyNoetherian_completeUniformGraphEmbedding_openCover
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤))) :
    ∃ C : Scheme.OpenCover.{u} S,
      (∀ i, IsAffine (C.X i)) ∧ (∀ i, IsNoetherianRing Γ(C.X i, ⊤)) ∧
      ∀ i, ∃ E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding (A.pullback (C.f i)).graphBundle
        (A.pullback (C.f i)).abelian.scheme.hom,
        E.degree = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ ∧
          E.dimension = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1 ∧ E.HasCompleteSections := by
  let V := S.affineOpenCover.openCover
  have h (i : V.I₀) : ∃ C : Scheme.OpenCover.{u} (V.X i),
      (∀ j, IsAffine (C.X j)) ∧ (∀ j, IsNoetherianRing Γ(C.X j, ⊤)) ∧
      ∀ j, ∃ E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding ((A.pullback (V.f i)).pullback (C.f j)).graphBundle
        ((A.pullback (V.f i)).pullback (C.f j)).abelian.scheme.hom,
        E.degree = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ ∧
          E.dimension = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1 ∧ E.HasCompleteSections := by
    let R := S.affineOpenCover.X i
    let : IsNoetherianRing R := Noetherian.AffineGluing.affineCoverCoordinateRing_noetherian S i
    let : IsAffine (V.X i) := inferInstanceAs (IsAffine (Spec R))
    let : IsNoetherianRing Γ(V.X i, ⊤) :=
      isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
    have hu : IsUnit (N : Γ(V.X i, ⊤)) := Abelian.Schemes.level_unit_under_base_change (V.f i) N hunit
    exact (A.pullback (V.f i)).exists_completeUniformGraphEmbedding_openCover hg hδ hN hu
  choose C ha hr hE using h
  let W := V.bind C
  refine ⟨W, fun i => ha i.1 i.2, fun i => hr i.1 i.2, ?_⟩
  rintro ⟨i, j⟩
  obtain ⟨E, hd, hn, hcomplete⟩ := hE i j
  let e := (Moduli.Isomorphisms.LevelPreservingIso.pullbackComp A (V.f i) ((C i).f j)).symm
  exact ⟨e.graphPowerEmbedding E, hd, hn,
    Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.HasCompleteSections.ofSourceIso E e.abelian e.graphBundleIso hcomplete⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
