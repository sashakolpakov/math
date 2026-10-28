import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.TorsionHyperplaneSparsity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.GeometricConfiguration

/-! # Hyperplane Sparsity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The ordered full-level configuration itself satisfies the strict
hyperplane sparsity inequality once the explicit square threshold is
met. Its distinct points and full n^(2g) cardinality are constructed
from the given full level. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u

theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPower_fullLevel_hyperplanes_sparse
    {K : Type u} [Field K] [IsAlgClosed K] {g N n : ℕ} {δ : Fin g → ℕ} [NeZero n]
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    (level : A.abelian.FullLevel n)
    (hlarge : Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ < n ^ 2)
    (a : Line.Bundles.structureModule A.abelian.scheme.left ⟶
      (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf) (ha : a ≠ 0) :
    Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ *
      (Finset.univ.filter (fun i => A.abelian.fullLevelGeometricPoint level i ∉ Ample.LineBundles.sectionNonvanishing a)).card <
        n ^ (2 * g) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have h := A.uniformGraphPower_torsion_hyperplanes_sparse hg hδ hN hNk n hn level hlarge
    (A.abelian.fullLevelGeometricPoint level) (A.abelian.fullLevelGeometricPoint_injective level)
    (by simp) (A.abelian.fullLevelGeometricPoint_multiplication level) a ha
  simpa only [show Fintype.card (Multiplicative (Fin (2 * g) → ZMod n)) = n ^ (2 * g) by simp] using h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
