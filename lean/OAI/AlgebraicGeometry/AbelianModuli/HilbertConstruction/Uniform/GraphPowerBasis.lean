import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.GraphSquareMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GraphSectionFactorization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.Powers

/-! # Graph Power Basis -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A uniform even graph power has a complete generating section basis of
explicit size, and its section map is finite over every tame field. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

def PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPowerSectionBasis (hg : 0 < g) (hδ : ∀ i, 0 < δ i)
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    Module.Basis (Fin (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1 + 1)) K
      ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj
        (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf) := by
  have := A.graphBundle_positivePower_sections_finite_overField (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
  apply Module.finBasisOfFinrankEq K _
  have he := A.graphBundle_positivePower_sections_finrank_normalized hg hN hNk
    (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ)
  change Module.finrank K ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj
    (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf) =
      Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ at he
  exact he.trans (Nat.sub_add_cancel
    (Nat.succ_le_of_lt (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank_pos g δ hδ))).symm

theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPower_pointwise_sections (hδ : ∀ i, 0 < δ i)
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    ∀ x : A.abelian.scheme.left,
      ∃ s : Line.Bundles.structureModule A.abelian.scheme.left ⟶
        (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf,
        x ∈ Ample.LineBundles.sectionNonvanishing s := by
  intro x
  obtain ⟨s, hs⟩ := A.graphBundle_square_pointwise_sections_overField hN hNk x
  let r := Graph.EmbeddingNumerics.graphSquareSectionRank g δ
  have hr : 0 < r := Graph.EmbeddingNumerics.graphSquareSectionRank_pos g δ hδ
  let e : ((A.graphBundle.tensorPower 2).tensorPower r).sheaf ≅
      (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf :=
    (A.graphBundle.tensorPowerComposeIso r 2).symm ≪≫
      eqToIso (congrArg (fun d => (A.graphBundle.tensorPower d).sheaf) (Nat.mul_comm r 2))
  refine ⟨TensorPower.Maps.tensorPowerSection s r ≫ e.hom, ?_⟩
  erw [Ample.Powers.sectionNonvanishing_comp_iso, Section.PowerLocus.sectionNonvanishing_tensorPowerSection s r hr]
  exact hs

def PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPowerSections (hg : 0 < g) (hδ : ∀ i, 0 < δ i)
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    Fin (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1 + 1) →
      (Line.Bundles.structureModule A.abelian.scheme.left ⟶
        (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf) :=
  BasisSectionGeneration.sectionBasisFamily A.abelian.scheme.hom
    (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf
    (A.uniformGraphPowerSectionBasis hg hδ hN hNk)

theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPowerSections_cover (hg : 0 < g) (hδ : ∀ i, 0 < δ i)
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    ∀ x : A.abelian.scheme.left,
      ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (A.uniformGraphPowerSections hg hδ hN hNk i) :=
  BasisSectionGeneration.sectionBasisFamily_covers A.abelian.scheme.hom
    (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ))
    (A.uniformGraphPowerSectionBasis hg hδ hN hNk) (A.uniformGraphPower_pointwise_sections hδ hN hNk)

theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPower_sectionMap_isFinite (hg : 0 < g) (hδ : ∀ i, 0 < δ i)
    (hN : 3 ≤ N) (hNk : (N : K) ≠ 0) :
    IsFinite (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom
      (A.uniformGraphPowerSections hg hδ hN hNk) (A.uniformGraphPowerSections_cover hg hδ hN hNk)).left := by
  apply GeometricallyAmpleSectionMorphism.sectionProjectiveMorphism_isFinite_of_geometric_ample A.abelian.scheme.hom
    (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)) _ _
  intro F _ _ f
  exact ((A.graphBundle_ample_geometricFiber F f).tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
    (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ)).of_iso
      (A.graphBundle.powerBaseChangeIso (CategoryTheory.Limits.pullback.fst A.abelian.scheme.hom f)
        (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
