import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GraphPowerEmbedding
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.PowerIntersectionData

/-! # Graph Intersection Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The uniform complete graph-power embedding supplies its actual
affine charts, generating section ratios, and Euler coefficient equal
to the prescribed section rank depending only on dimension and type. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree (g : ℕ) (δ : Fin g → ℕ) : ℕ :=
  Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * g.factorial

variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
variable (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)

theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPowerSections_ratios_generate :
    Section.ProjectivePresentation.SectionRatiosGenerate A.abelian.scheme.hom (A.uniformGraphPowerSections hg hδ hN hNk) := by
  have : CompactSpace A.abelian.scheme.left := QuasiCompact.compactSpace_of_compactSpace A.abelian.scheme.hom
  have : A.abelian.scheme.left.IsSeparated := ⟨by
    rw [← terminal.comp_from A.abelian.scheme.hom]; infer_instance⟩
  apply Power.FactorizationBasisEmbedding.sectionBasisFamily_ratios_generate A.abelian.scheme.hom
    (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ))
    (A.uniformGraphPowerSectionBasis hg hδ hN hNk)
  intro m hm
  simpa only [Graph.EmbeddingNumerics.graphUniformEmbeddingDegree, Nat.add_comm 1 m] using
    A.graphBundle_uniform_power_consecutive_sections_factor hg hδ hN hNk m hm

theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPowerSections_affine (i : Fin (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1 + 1)) :
    IsAffineOpen (Ample.LineBundles.sectionNonvanishing (A.uniformGraphPowerSections hg hδ hN hNk i)) := by
  let p := A.abelian.scheme.hom
  let s := A.uniformGraphPowerSections hg hδ hN hNk
  let hs := A.uniformGraphPowerSections_cover hg hδ hN hNk
  let a := SectionsProjectiveMorphism.sectionAbsoluteMorphism p s hs
  let q := pullback.fst (Projective.ProjectivePresentations.affineProjectiveSpace Γ(Spec (.of K), ⊤)
    (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1)).hom (Spec (.of K)).toSpecΓ
  have : IsIso q := inferInstance
  have he : (SectionsProjectiveMorphism.sectionProjectiveMorphism p s hs).left ≫ q = a := pullback.lift_fst _ _ _
  have : IsFinite (SectionsProjectiveMorphism.sectionProjectiveMorphism p s hs).left :=
    A.uniformGraphPower_sectionMap_isFinite hg hδ hN hNk
  have : IsFinite q := inferInstance
  have : IsFinite a := he ▸ (MorphismProperty.comp_mem (@IsFinite)
    (SectionsProjectiveMorphism.sectionProjectiveMorphism p s hs).left q inferInstance inferInstance)
  have h := (StandardProjectiveCharts.standardProjectiveChart_isAffine Γ(Spec (.of K), ⊤)
    (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ - 1) i).preimage a
  erw [ProjectiveChart.Preimages.sectionAbsoluteMorphism_preimage] at h
  exact h

include hg hδ hN hNk in
theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPower_euler_eq_sectionRank :
    CohomologyEulerCharacteristic.coefficientEulerCharacteristic A.abelian.scheme.hom
      (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf =
        (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ : ℤ) := by
  have hunit : IsUnit (N : Γ(Spec (.of K), ⊤)) := by
    simpa only [map_natCast] using
      (isUnit_iff_ne_zero.mpr hNk).map (Coefficient.ModulePresheaf.schemeCoefficientMap (𝟙 (Spec (.of K))))
  rw [A.graphBundle_positivePower_euler_eq_sections hN hunit
    (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ)]
  exact congrArg (fun n : ℕ => (n : ℤ))
    (A.graphBundle_positivePower_sections_finrank_normalized hg hN hNk
      (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
