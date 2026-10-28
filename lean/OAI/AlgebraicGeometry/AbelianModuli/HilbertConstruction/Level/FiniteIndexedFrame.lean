import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.EvaluationProjectiveFrame
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.IndexedProjectiveFrames

/-! # Finite Indexed Frame -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The torsion frame uses a fixed finite list of labels of length equal
to the uniform section rank, followed by its additional frame point. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem PolarizationData.PolarizedAbelianWithFullLevel.fullLevelSectionEvaluation_finiteIndexedFrame
    {K : Type u} [Field K] [IsAlgClosed K] {g N n : ℕ} {δ : Fin g → ℕ} [NeZero n]
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    (level : A.abelian.FullLevel n)
    (hlarge : Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ < n ^ 2) :
    HilbertConstruction.Finite.IndexedProjectiveFrames.HasFiniteIndexedProjectiveFrame (K := K) (r := Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ)
      (A.fullLevelSectionEvaluation level) := by
  let L := A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
  let V := (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor A.abelian.scheme.hom).obj L.sheaf
  have : Module.Finite K V :=
    A.graphBundle_positivePower_sections_finite_overField (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)
  apply HilbertConstruction.Finite.IndexedProjectiveFrames.hasFiniteIndexedProjectiveFrame_of_basis (A.fullLevelSectionEvaluation level)
  · rw [Subspace.dual_finrank_eq]
    exact A.graphBundle_positivePower_sections_finrank_normalized hg hN hNk
      (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ) (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ)
  · exact A.fullLevelSectionEvaluation_projectiveFrame hg hδ hN hNk level hlarge

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
