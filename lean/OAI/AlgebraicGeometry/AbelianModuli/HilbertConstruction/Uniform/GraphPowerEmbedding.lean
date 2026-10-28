import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GraphPowerBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.FactorizationBasisEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.ProjectiveEmbeddings

/-! # Graph Power Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! An explicit graph power gives a closed embedding over every tame field.
Both its exponent and the dimension of its complete section system depend
only on the relative dimension and polarization type. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
variable (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)

theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPower_sectionMap_closedImmersion :
    IsClosedImmersion (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom
      (A.uniformGraphPowerSections hg hδ hN hNk) (A.uniformGraphPowerSections_cover hg hδ hN hNk)).left := by
  have : CompactSpace A.abelian.scheme.left :=
    QuasiCompact.compactSpace_of_compactSpace A.abelian.scheme.hom
  have : A.abelian.scheme.left.IsSeparated :=
    ⟨(terminal.comp_from A.abelian.scheme.hom) ▸
      (inferInstance : IsSeparated (A.abelian.scheme.hom ≫ terminal.from (Spec (.of K))))⟩
  have : IsFinite (SectionsProjectiveMorphism.sectionProjectiveMorphism A.abelian.scheme.hom
      (BasisSectionGeneration.sectionBasisFamily A.abelian.scheme.hom
        (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf
        (A.uniformGraphPowerSectionBasis hg hδ hN hNk))
      (A.uniformGraphPowerSections_cover hg hδ hN hNk)).left :=
    A.uniformGraphPower_sectionMap_isFinite hg hδ hN hNk
  apply Power.FactorizationBasisEmbedding.sectionBasisFamily_closedImmersion_of_finite A.abelian.scheme.hom
    (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ))
    (A.uniformGraphPowerSectionBasis hg hδ hN hNk) _ (A.uniformGraphPowerSections_cover hg hδ hN hNk)
  intro m hm
  simpa only [Graph.EmbeddingNumerics.graphUniformEmbeddingDegree, Nat.add_comm 1 m] using
    A.graphBundle_uniform_power_consecutive_sections_factor hg hδ hN hNk m hm

def PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPowerEmbedding : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom where
  degree := Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ
  degree_pos := Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ
  power := A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
  isPower := A.graphBundle.tensorPower_isTensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
  dimension := Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1
  sections := A.uniformGraphPowerSections hg hδ hN hNk
  covers := A.uniformGraphPowerSections_cover hg hδ hN hNk
  closedImmersion := A.uniformGraphPower_sectionMap_closedImmersion hg hδ hN hNk

theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPowerEmbedding_degree :
    (A.uniformGraphPowerEmbedding hg hδ hN hNk).degree = Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ := rfl

theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPowerEmbedding_dimension :
    (A.uniformGraphPowerEmbedding hg hδ hN hNk).dimension = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1 := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
