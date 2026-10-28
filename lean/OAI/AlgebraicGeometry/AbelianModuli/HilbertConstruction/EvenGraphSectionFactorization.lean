import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GraphSectionFactorization

/-! # Even Graph Section Factorization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Every sufficiently large even graph power has the consecutive
section-factorization property, with the same uniform lower bound. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_large_even_consecutive_sections_factor
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)
    (t : ℕ) (ht : Graph.EmbeddingNumerics.graphSquareSectionRank g δ ≤ t) (m : ℕ) (hm : 0 < m) :
    Section.FactorizationSpans.SectionFactorizationSpan (Line.Bundles.structureModule A.abelian.scheme.left)
      ((A.graphBundle.tensorPower (2 * t)).tensorPower m).sheaf
      ((A.graphBundle.tensorPower (2 * t)).tensorPower (m + 1)).sheaf := by
  have hq : 2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ - 1 ≤ m * (2 * t) := by
    have hmul := Nat.mul_le_mul_right (2 * t) (Nat.succ_le_of_lt hm)
    have hsize := Nat.mul_le_mul_left 2 ht
    omega
  have h := A.graphBundle_even_steps_sections_factor hg hδ hN hNk (m * (2 * t)) hq t
  have heq : 2 * t + m * (2 * t) = (m + 1) * (2 * t) := by ring
  rw [heq] at h
  exact (h.sourceIso (A.graphBundle.tensorPowerComposeIso m (2 * t))).targetIso
    (A.graphBundle.tensorPowerComposeIso (m + 1) (2 * t))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
