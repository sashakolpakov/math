import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GraphSectionLocalBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.LocalizationSectionBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.UniformGraphBasisEmbedding

/-! # Uniform Graph Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Around every prime of a Noetherian affine tame base there is an actual
relative closed embedding of the polarized family by the same graph power,
into projective space of the same dimension. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
variable {g N : ℕ} {δ : Fin g → ℕ} (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.exists_local_uniformGraphPowerEmbedding
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    (p : PrimeSpectrum Γ(S, ⊤)) :
    ∃ r : Γ(S, ⊤), r ∉ p.asIdeal ∧
      ∃ E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding
        (A.pullback (Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(S, ⊤) (Localization.Away r)))).graphBundle
        (A.pullback (Affine.QuotientCoefficientMap.affineCoordinateMap (algebraMap Γ(S, ⊤) (Localization.Away r)))).abelian.scheme.hom,
      E.degree = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ ∧
        E.dimension = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1 := by
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
  have : IsNoetherianRing R := inferInstance
  have : IsNoetherianRing Γ(Spec (.of R), ⊤) :=
    isNoetherianRing_of_ringEquiv R (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  have hN' : IsUnit (N : Γ(Spec (.of R), ⊤)) := Abelian.Schemes.level_unit_under_base_change b N hunit
  let E := C.uniformGraphPowerEmbeddingOfCoefficientBasis hg hδ hN hN' BC
  exact ⟨r, hr, E, rfl, rfl⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
