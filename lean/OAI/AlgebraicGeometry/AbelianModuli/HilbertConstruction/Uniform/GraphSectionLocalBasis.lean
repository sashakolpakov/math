import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ModuleResidueRank
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.UniformGraphPowerGeneration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.FieldSectionIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.FlatAlgebraLocalBasis

/-! # Graph Section Local Basis -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The fixed graph-power section module has its prescribed rank at every
prime and an actual basis of that size on a principal neighborhood. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
variable {g N : ℕ} {δ : Fin g → ℕ} (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

def PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphSectionModule : ModuleCat.{u} Γ(S, ⊤) :=
  (Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor A.abelian.scheme.hom.appTop.hom).obj
    (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf

theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphSectionModule_rankAtStalk
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    (p : PrimeSpectrum Γ(S, ⊤)) :
    Module.rankAtStalk A.uniformGraphSectionModule p = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ := by
  obtain ⟨hf, hp⟩ := A.uniformGraphPower_sections_finite_projective hδ hN hunit
  have : Module.Finite Γ(S, ⊤) ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor
      A.abelian.scheme.hom.appTop.hom).obj
      (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf) := hf
  have : Module.Projective Γ(S, ⊤) ((Coefficient.GlobalSectionsFunctor.coefficientGlobalSectionsFunctor
      A.abelian.scheme.hom.appTop.hom).obj
      (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf) := hp
  let x := S.isoSpec.inv p
  have hx : S.toSpecΓ x = p :=
    congrArg (fun f : Spec Γ(S, ⊤) ⟶ Spec Γ(S, ⊤) => f p) S.isoSpec.inv_hom_id
  calc
    Module.rankAtStalk A.uniformGraphSectionModule p =
        Module.rankAtStalk A.uniformGraphSectionModule (S.toSpecΓ x) :=
      congrArg (Module.rankAtStalk A.uniformGraphSectionModule) hx.symm
    _ = FiberEulerGroundField.lineBundleFieldSectionDimension (A.abelian.scheme.hom.fiberToSpecResidueField x)
        ((A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).pullback
          (A.abelian.scheme.hom.fiberι x)) :=
      Section.ModuleResidueRank.sectionModule_rankAtStalk_of_residueComparison A.abelian.scheme.hom
        (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)) x
        (A.graphBundle_positivePower_fieldSectionTensorComparison_bijective hN hunit
          (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ)
          (S.fromSpecResidueField x))
    _ = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ :=
      A.uniformGraphPower_residueFiberSections_dimension hg hδ hN hunit x

theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphSectionModule_localBasis
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤)))
    (p : PrimeSpectrum Γ(S, ⊤)) :
    ∃ a : Γ(S, ⊤), a ∉ p.asIdeal ∧ Nonempty
      (Module.Basis (Fin (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1 + 1))
        (Localization.Away a) (LocalizedModule.Away a A.uniformGraphSectionModule)) := by
  obtain ⟨hf, hp⟩ := A.uniformGraphPower_sections_finite_projective hδ hN hunit
  have : Module.Finite Γ(S, ⊤) A.uniformGraphSectionModule := hf
  have : Module.Projective Γ(S, ⊤) A.uniformGraphSectionModule := hp
  have : Module.FinitePresentation Γ(S, ⊤) A.uniformGraphSectionModule :=
    Module.finitePresentation_of_projective Γ(S, ⊤) A.uniformGraphSectionModule
  exact HilbertConstruction.Finite.FlatAlgebraLocalBasis.finiteFlat_exists_localModuleBasis A.uniformGraphSectionModule p
    ((A.uniformGraphSectionModule_rankAtStalk hg hδ hN hunit p).trans
      (Nat.sub_add_cancel (Nat.succ_le_of_lt (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank_pos g δ hδ))).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
