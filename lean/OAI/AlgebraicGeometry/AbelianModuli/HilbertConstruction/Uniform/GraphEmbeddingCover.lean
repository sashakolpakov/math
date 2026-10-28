import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.UniformGraphEmbedding

/-! # Graph Embedding Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The local uniform embeddings assemble into an actual affine open cover
of every Noetherian affine tame base. Each member has the fixed exponent
and ambient projective dimension. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem Uniform.GraphEmbeddingCover.affineLocalizationPoint_mem_range {S : Scheme.{u}} [IsAffine S]
    (r : Γ(S, ⊤)) (x : S) (hr : r ∉ (S.toSpecΓ x).asIdeal) :
    x ∈ Set.range (Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(S, ⊤) (Localization.Away r))) := by
  obtain ⟨p, hp⟩ : S.toSpecΓ x ∈ Set.range
      (PrimeSpectrum.comap (algebraMap Γ(S, ⊤) (Localization.Away r))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  refine ⟨p, ?_⟩
  change S.isoSpec.inv (p.comap (algebraMap Γ(S, ⊤) (Localization.Away r))) = x
  rw [hp]
  exact congrArg (fun f : S ⟶ S => f x) S.isoSpec.hom_inv_id

variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
variable {g N : ℕ} {δ : Fin g → ℕ} (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.exists_uniformGraphEmbedding_openCover
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤))) :
    ∃ C : Scheme.OpenCover.{u} S,
      (∀ i, IsAffine (C.X i)) ∧
      (∀ i, IsNoetherianRing Γ(C.X i, ⊤)) ∧
      ∀ i, ∃ E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding (A.pullback (C.f i)).graphBundle
        (A.pullback (C.f i)).abelian.scheme.hom,
        E.degree = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ ∧
          E.dimension = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1 := by
  choose r hr E hd hn using fun x : S =>
    A.exists_local_uniformGraphPowerEmbedding hg hδ hN hunit (S.toSpecΓ x)
  let b (x : S) := Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(S, ⊤) (Localization.Away (r x)))
  have (x : S) : IsOpenImmersion (b x) := Affine.LocalizationSectionBasis.affineLocalizationPoint_isOpenImmersion (r x)
  let C : Scheme.OpenCover.{u} S := {
    I₀ := S
    X x := Spec (.of (Localization.Away (r x)))
    f x := b x
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨fun x => ⟨x, Uniform.GraphEmbeddingCover.affineLocalizationPoint_mem_range (r x) x (hr x)⟩, inferInstance⟩ }
  refine ⟨C, fun _ => inferInstance, ?_, fun x => ⟨E x, hd x, hn x⟩⟩
  intro x
  exact isNoetherianRing_of_ringEquiv (Localization.Away (r x))
    (Scheme.ΓSpecIso (.of (Localization.Away (r x)))).symm.commRingCatIsoToRingEquiv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
