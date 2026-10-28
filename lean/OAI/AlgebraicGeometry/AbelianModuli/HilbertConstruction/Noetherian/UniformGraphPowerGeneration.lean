import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GraphPowerBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.GraphSquareGeneration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GraphPower.SectionsProjective
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.GraphResidueFiberDimensions

/-! # Uniform Graph Power Generation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The same uniform graph power is globally generated over Noetherian
affine tame bases. Its section module is finite projective, and its actual
residue-fiber section dimension has the fixed embedding value. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
variable {g N : ℕ} {δ : Fin g → ℕ} (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPower_pointwise_sections_noetherian_affine
    (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤))) :
    ∀ x : A.abelian.scheme.left,
      ∃ s : Line.Bundles.structureModule A.abelian.scheme.left ⟶
        (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf,
        x ∈ Ample.LineBundles.sectionNonvanishing s := by
  intro x
  obtain ⟨s, hs⟩ := A.graphBundle_square_pointwise_sections_noetherian_affine hN hunit x
  let r := Graph.EmbeddingNumerics.graphSquareSectionRank g δ
  have hr : 0 < r := Graph.EmbeddingNumerics.graphSquareSectionRank_pos g δ hδ
  let e : ((A.graphBundle.tensorPower 2).tensorPower r).sheaf ≅
      (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf :=
    (A.graphBundle.tensorPowerComposeIso r 2).symm ≪≫
      eqToIso (congrArg (fun d => (A.graphBundle.tensorPower d).sheaf) (Nat.mul_comm r 2))
  refine ⟨TensorPower.Maps.tensorPowerSection s r ≫ e.hom, ?_⟩
  erw [Ample.Powers.sectionNonvanishing_comp_iso, Section.PowerLocus.sectionNonvanishing_tensorPowerSection s r hr]
  exact hs

theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPower_finite_section_cover_noetherian_affine
    (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤))) :
    ∃ (n : ℕ) (s : Fin (n + 1) → (Line.Bundles.structureModule A.abelian.scheme.left ⟶
        (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf)),
      ∀ x : A.abelian.scheme.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i) := by
  have : CompactSpace A.abelian.scheme.left :=
    QuasiCompact.compactSpace_of_compactSpace A.abelian.scheme.hom
  exact (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).finite_section_cover_of_pointwise
    (A.uniformGraphPower_pointwise_sections_noetherian_affine hδ hN hunit)

theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPower_sections_finite_projective
    (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤))) :
    Module.Finite Γ(S, ⊤) ((Coefficient.ModulePresheaf.coefficientModulePresheaf A.abelian.scheme.hom.appTop.hom
      (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf).obj (op ⊤)) ∧
    Module.Projective Γ(S, ⊤) ((Coefficient.ModulePresheaf.coefficientModulePresheaf A.abelian.scheme.hom.appTop.hom
      (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf).obj (op ⊤)) :=
  A.graphBundle_positivePower_sections_finite_projective hN hunit
    (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ)

omit [IsAffine S] [IsNoetherianRing Γ(S, ⊤)] in
theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPower_residueFiberSections_dimension
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hunit : IsUnit (N : Γ(S, ⊤))) (x : S) :
    FiberEulerGroundField.lineBundleFieldSectionDimension (A.abelian.scheme.hom.fiberToSpecResidueField x)
      ((A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).pullback
        (A.abelian.scheme.hom.fiberι x)) = Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ :=
  A.graphBundle_positivePower_residueFiberSections_normalized hg hN hunit
    (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ) x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
