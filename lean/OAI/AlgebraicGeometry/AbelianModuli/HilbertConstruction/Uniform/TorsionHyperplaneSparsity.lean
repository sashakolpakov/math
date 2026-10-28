import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.TorsionHyperplaneBound
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AuxiliaryLevelFrameBounds

/-! # Torsion Hyperplane Sparsity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Once n² exceeds the fixed section rank times D, every nonzero
hyperplane contains strictly fewer than one section-rank-th of a full
n-torsion configuration. This is the numerical input for projective
frame selection, with D supplied by the actual intersection bound. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj Classical
universe u v

theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPower_torsion_hyperplanes_sparse
    {K : Type u} [Field K] [IsAlgClosed K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    (n : ℕ) (hn : 0 < n) (level : A.abelian.FullLevel n)
    (hlarge : Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ < n ^ 2)
    {κ : Type v} [Fintype κ] (x : κ → A.abelian.scheme.left) (hx : Function.Injective x)
    (hcard : Fintype.card κ = n ^ (2 * g))
    (hxn : ∀ i, (A.abelian.multiplication n).left (x i) =
      η[A.abelian.scheme].left (IsLocalRing.closedPoint K))
    (a : Line.Bundles.structureModule A.abelian.scheme.left ⟶
      (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf) (ha : a ≠ 0) :
    Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ *
      (Finset.univ.filter (fun i => x i ∉ Ample.LineBundles.sectionNonvanishing a)).card < Fintype.card κ := by
  let J := Finset.univ.filter (fun i => x i ∉ Ample.LineBundles.sectionNonvanishing a)
  have hcount := A.uniformGraphPower_torsion_hyperplane_card_le hg hδ hN hNk n hn level a ha
    (fun i : J => x i.val)
    (fun i j h => Subtype.ext (hx h))
    (fun i => (Finset.mem_filter.mp i.property).2) (fun i => hxn i.val)
  have hcount' : J.card ≤ Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ * n ^ (2 * g - 2) := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using hcount
  rw [hcard]
  exact AuxiliaryLevelFrameBounds.torsionCount_sparse_of_degree_bound g (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ)
    (Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ) n J.card hg hn hlarge hcount'

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
