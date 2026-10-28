import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.HyperplaneSparsity

/-! # Sparse Uniform Level Configuration -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A formulation of the actual full-level hyperplane bound independent
of chosen finite-type instances on its ordered label set. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u

def PolarizationData.PolarizedAbelianWithFullLevel.SparseUniformFullLevelConfiguration
    {K : Type u} [Field K] {g N n : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (level : A.abelian.FullLevel n) : Prop :=
  ∀ a : Line.Bundles.structureModule A.abelian.scheme.left ⟶
      (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf,
    a ≠ 0 → Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ *
      Nat.card {c : Multiplicative (Fin (2 * g) → ZMod n) //
        A.abelian.fullLevelGeometricPoint level c ∉ Ample.LineBundles.sectionNonvanishing a} < n ^ (2 * g)

theorem PolarizationData.PolarizedAbelianWithFullLevel.sparseUniformFullLevelConfiguration_of_square_bound
    {K : Type u} [Field K] [IsAlgClosed K] {g N n : ℕ} {δ : Fin g → ℕ} [NeZero n]
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    (level : A.abelian.FullLevel n)
    (hlarge : Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ < n ^ 2) :
    A.SparseUniformFullLevelConfiguration level := by
  intro a ha
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact A.uniformGraphPower_fullLevel_hyperplanes_sparse hg hδ hN hNk level hlarge a ha

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
