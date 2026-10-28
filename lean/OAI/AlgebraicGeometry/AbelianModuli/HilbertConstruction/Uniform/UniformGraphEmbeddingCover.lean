import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.LocalUniformGraphEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GraphEmbeddingCover

/-! # Uniform Graph Embedding Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A Noetherian affine tame base has an affine open cover carrying
uniform graph embeddings together with their complete section bases. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
variable {g N : ℕ} {δ : Fin g → ℕ} (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.exists_completeUniformGraphEmbedding_openCover
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤))) :
    ∃ C : Scheme.OpenCover.{u} S,
      (∀ i, IsAffine (C.X i)) ∧ (∀ i, IsNoetherianRing Γ(C.X i, ⊤)) ∧
      ∀ i, ∃ E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding (A.pullback (C.f i)).graphBundle
        (A.pullback (C.f i)).abelian.scheme.hom,
        E.degree = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ ∧
          E.dimension = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1 ∧ E.HasCompleteSections := by
  choose r hr E hd hn hcomplete using fun x : S =>
    A.exists_local_completeUniformGraphPowerEmbedding hg hδ hN hunit (S.toSpecΓ x)
  let b (x : S) := Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(S, ⊤) (Localization.Away (r x)))
  have (x : S) : IsOpenImmersion (b x) := Affine.LocalizationSectionBasis.affineLocalizationPoint_isOpenImmersion (r x)
  let C : Scheme.OpenCover.{u} S := {
    I₀ := S
    X x := Spec (.of (Localization.Away (r x)))
    f x := b x
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun x => ⟨x, Uniform.GraphEmbeddingCover.affineLocalizationPoint_mem_range (r x) x (hr x)⟩, inferInstance⟩ }
  refine ⟨C, fun _ => inferInstance, ?_, fun x => ⟨E x, hd x, hn x, hcomplete x⟩⟩
  intro x
  exact isNoetherianRing_of_ringEquiv (Localization.Away (r x))
    (Scheme.ΓSpecIso (.of (Localization.Away (r x)))).symm.commRingCatIsoToRingEquiv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
