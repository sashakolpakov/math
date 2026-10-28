import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.PowerTorsionHyperplaneBound
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GraphIntersectionData

/-! # Torsion Hyperplane Bound -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! In the fixed complete graph-power embedding, every nonzero
hyperplane contains at most D n^(2g-2) distinct n-torsion points, where
D is the explicit section rank times g! and depends only on g and δ. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem PolarizationData.PolarizedAbelianWithFullLevel.uniformGraphPower_torsion_hyperplane_card_le
    {K : Type u} [Field K] [IsAlgClosed K] {g N : ℕ} {δ : Fin g → ℕ}
    (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    (n : ℕ) (hn : 0 < n) (level : A.abelian.FullLevel n)
    (a : Line.Bundles.structureModule A.abelian.scheme.left ⟶
      (A.graphBundle.tensorPower (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ)).sheaf) (ha : a ≠ 0)
    {κ : Type v} [Finite κ] (x : κ → A.abelian.scheme.left) (hx : Function.Injective x)
    (hxa : ∀ i, x i ∉ Ample.LineBundles.sectionNonvanishing a)
    (hxn : ∀ i, (A.abelian.multiplication n).left (x i) =
      η[A.abelian.scheme].left (IsLocalRing.closedPoint K)) :
    Nat.card κ ≤ Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ * n ^ (2 * g - 2) := by
  cases g with
  | zero => omega
  | succ g =>
    have h := A.graphBundlePower_torsion_hyperplane_card_le hN hNk
      (Graph.EmbeddingNumerics.graphUniformEmbeddingDegree (g + 1) δ)
      (A.uniformGraphPowerSections hg hδ hN hNk)
      (A.uniformGraphPowerSections_cover hg hδ hN hNk)
      (A.uniformGraphPowerSections_affine hg hδ hN hNk)
      (A.uniformGraphPowerSections_ratios_generate hg hδ hN hNk)
      n hn level a ha x hx hxa hxn
    rw [A.uniformGraphPower_euler_eq_sectionRank hg hδ hN hNk] at h
    change Nat.card κ ≤
      (Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank (g + 1) δ * (g + 1).factorial) * n ^ (2 * (g + 1) - 2)
    rw [show 2 * (g + 1) - 2 = 2 * g by omega]
    exact_mod_cast h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
