import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.UniformGraphEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PowerEmbedding.Sections

/-! # Local Uniform Graph Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.LocalUniformGraphEmbedding.PolarizedAbelianWithLevel

noncomputable section

/-! The local uniform graph embedding is made from a complete section
basis; retain that basis in the existence conclusion. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem coefficientEmbedding_complete {R : Type u} [CommRing R]
    [IsNoetherianRing Γ(Spec (.of R), ⊤)] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of R)))
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N)
    (hunit : IsUnit (N : Γ(Spec (.of R), ⊤)))
    (B : Module.Basis (Fin (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1 + 1)) Γ(Spec (.of R), ⊤)
      ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor A.abelian.scheme.hom.appTop.hom).obj
        (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf)) :
    (A.uniformGraphPowerEmbeddingOfCoefficientBasis hg hδ hN hunit B).HasCompleteSections :=
  ⟨⟨B, rfl⟩⟩

variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
variable {g N : ℕ} {δ : Fin g → ℕ} (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.exists_local_completeUniformGraphPowerEmbedding
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    (p : PrimeSpectrum Γ(S, ⊤)) :
    ∃ r : Γ(S, ⊤), r ∉ p.asIdeal ∧
      ∃ E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding
        (A.pullback (Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(S, ⊤) (Localization.Away r)))).graphBundle
        (A.pullback (Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(S, ⊤) (Localization.Away r)))).abelian.scheme.hom,
      E.degree = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ ∧
        E.dimension = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1 ∧ E.HasCompleteSections := by
  obtain ⟨r, hr, ⟨B⟩⟩ := A.uniformGraphSectionModule_localBasis hg hδ hN hunit p
  let R := Localization.Away r
  let b := Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(S, ⊤) R)
  let C := A.pullback b
  let a := pullback.fst A.abelian.scheme.hom b
  let d := Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ
  let e : ((A.graphBundle.tensorPower d).pullback a).sheaf ≅ (C.graphBundle.tensorPower d).sheaf :=
    A.graphBundle.powerBaseChangeIso a d ≪≫
      (TensorPower.Maps.tensorPowerFunctor C.abelian.scheme.left d).mapIso (A.graphBundle_baseChangeIso b).symm
  let BL := Affine.LocalizationSectionBasis.affineLocalizationSectionBasis A.abelian.scheme.hom (A.graphBundle.tensorPower d) r B
  let BC : Module.Basis (Fin (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1 + 1)) Γ(Spec (.of R), ⊤)
      ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor C.abelian.scheme.hom.appTop.hom).obj
        (C.graphBundle.tensorPower d).sheaf) :=
    BL.map (((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor C.abelian.scheme.hom.appTop.hom).mapIso e).toLinearEquiv)
  let : IsNoetherianRing R := inferInstance
  let : IsNoetherianRing Γ(Spec (.of R), ⊤) :=
    isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  have hN' : IsUnit (N : Γ(Spec (.of R), ⊤)) := Abelian.Schemes.level_unit_under_base_change b N hunit
  let E := C.uniformGraphPowerEmbeddingOfCoefficientBasis hg hδ hN hN' BC
  have hE := coefficientEmbedding_complete C hg hδ hN hN' BC
  exact ⟨r, hr, E, rfl, rfl, hE⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.LocalUniformGraphEmbedding.PolarizedAbelianWithLevel
