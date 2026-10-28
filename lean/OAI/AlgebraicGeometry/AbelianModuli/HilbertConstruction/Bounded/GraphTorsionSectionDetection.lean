import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EvenGraphTorsionBound
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Level.GeometricConfiguration
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AuxiliaryLevelFrameBounds

/-! # Graph Torsion Section Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A sufficiently high full level detects every section in all
positive graph powers up to a prescribed degree bound. This supplies
the numerical input for detecting the bounded Hilbert equations. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u

theorem Bounded.GraphTorsionSectionDetection.evenGraphTorsionDegree_mono (g : ℕ) (δ : Fin g → ℕ) {s t : ℕ} (h : s ≤ t) :
    EvenGraphTorsionBound.evenGraphTorsionDegree g δ s ≤ EvenGraphTorsionBound.evenGraphTorsionDegree g δ t := by
  apply Nat.mul_le_mul_right g.factorial
  apply Nat.mul_le_mul_left _
  exact Nat.pow_le_pow_left (Nat.mul_le_mul_left 2 h) g

def Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree (g : ℕ) (δ : Fin g → ℕ) (B : ℕ) : ℕ :=
  EvenGraphTorsionBound.evenGraphTorsionDegree g δ (Graph.EmbeddingNumerics.graphSquareSectionRank g δ * max 1 B)

variable {K : Type u} [Field K] [IsAlgClosed K] {g N n : ℕ} {δ : Fin g → ℕ} [NeZero n]
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.evenGraphPower_section_eq_zero_of_fullLevel_vanishing
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    (t : ℕ) (ht : 0 < t) (htlarge : Graph.EmbeddingNumerics.graphSquareSectionRank g δ ≤ t)
    (level : A.abelian.FullLevel n) (hlarge : EvenGraphTorsionBound.evenGraphTorsionDegree g δ t < n ^ 2)
    (a : Line.Bundles.structureModule A.abelian.scheme.left ⟶ (A.graphBundle.tensorPower (2 * t)).sheaf)
    (ha : ∀ c, A.abelian.fullLevelGeometricPoint level c ∉ Ample.LineBundles.sectionNonvanishing a) : a = 0 := by
  by_contra hne
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hc := A.evenGraphPower_torsion_section_card_le hg hδ hN hNk t ht htlarge n hn level a hne
    (A.abelian.fullLevelGeometricPoint level) (A.abelian.fullLevelGeometricPoint_injective level)
    ha (A.abelian.fullLevelGeometricPoint_multiplication level)
  have hc' : n ^ (2 * g) ≤ EvenGraphTorsionBound.evenGraphTorsionDegree g δ t * n ^ (2 * g - 2) := by
    simpa using hc
  have hstrict := AuxiliaryLevelFrameBounds.torsionCount_sparse_of_degree_bound g 1 (EvenGraphTorsionBound.evenGraphTorsionDegree g δ t) n
    (n ^ (2 * g)) hg hn (by simpa only [one_mul] using hlarge) hc'
  exact (Nat.lt_irrefl _) (by simpa only [one_mul] using hstrict)

theorem PolarizationData.PolarizedAbelianWithFullLevel.boundedGraphPower_section_eq_zero_of_fullLevel_vanishing
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    (B : ℕ) (level : A.abelian.FullLevel n) (hlarge : Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ B < n ^ 2)
    (d : ℕ) (hd : 0 < d) (hdB : d ≤ B)
    (a : Line.Bundles.structureModule A.abelian.scheme.left ⟶
      (A.graphBundle.tensorPower (2 * (Graph.EmbeddingNumerics.graphSquareSectionRank g δ * d))).sheaf)
    (ha : ∀ c, A.abelian.fullLevelGeometricPoint level c ∉ Ample.LineBundles.sectionNonvanishing a) : a = 0 := by
  apply A.evenGraphPower_section_eq_zero_of_fullLevel_vanishing hg hδ hN hNk
    (Graph.EmbeddingNumerics.graphSquareSectionRank g δ * d) (Nat.mul_pos (Graph.EmbeddingNumerics.graphSquareSectionRank_pos g δ hδ) hd)
    (by simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left (Graph.EmbeddingNumerics.graphSquareSectionRank g δ) (Nat.succ_le_of_lt hd)) level
  · exact (Bounded.GraphTorsionSectionDetection.evenGraphTorsionDegree_mono g δ
      (Nat.mul_le_mul_left (Graph.EmbeddingNumerics.graphSquareSectionRank g δ) (hdB.trans (Nat.le_max_right 1 B)))).trans_lt hlarge
  · exact ha

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
