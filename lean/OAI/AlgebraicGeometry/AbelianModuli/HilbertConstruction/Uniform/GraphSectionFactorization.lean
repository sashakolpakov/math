import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.FactorizationSpans
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GraphSectionMultiplication
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Iterated.Powers

/-! # Graph Section Factorization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! The uniform two-degree multiplication step composes into arbitrary even
steps. Consequently consecutive powers of `G^(2r)` have a finite section factorization. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type u} [Field K] {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N (Spec (.of K)))
variable (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (hNk : (N : K) ≠ 0)

include hg hδ hN hNk

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_square_sections_factor
    (q : ℕ) (hq : 2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ - 1 ≤ q) :
    Section.FactorizationSpans.SectionFactorizationSpan (Line.Bundles.structureModule A.abelian.scheme.left)
      (A.graphBundle.tensorPower q).sheaf (A.graphBundle.tensorPower (2 + q)).sheaf := by
  intro t
  obtain ⟨n, s, v, ht⟩ :=
    A.graphBundle_square_multiplication_uniformly_surjective hg hδ hN hNk q hq t
  refine ⟨n, v, fun i =>
    Module.SectionMultiplication.moduleSectionMultiply (A.graphBundle.tensorPower 2) (A.graphBundle.tensorPower q).sheaf (s i) ≫
      (A.graphBundle.tensorPowerAddIso 2 q).inv, ?_⟩
  simpa only [← Category.assoc, Section.MultiplicationProduct.section_comp_moduleSectionMultiply] using ht

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_even_steps_sections_factor
    (q : ℕ) (hq : 2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ - 1 ≤ q) (k : ℕ) :
    Section.FactorizationSpans.SectionFactorizationSpan (Line.Bundles.structureModule A.abelian.scheme.left)
      (A.graphBundle.tensorPower q).sheaf (A.graphBundle.tensorPower (2 * k + q)).sheaf := by
  induction k with
  | zero => simpa only [Nat.mul_zero, Nat.zero_add] using
      (Section.FactorizationSpans.SectionFactorizationSpan.refl (Line.Bundles.structureModule A.abelian.scheme.left) (A.graphBundle.tensorPower q).sheaf)
  | succ k ih =>
    have h := ih.trans (A.graphBundle_square_sections_factor hg hδ hN hNk (2 * k + q) (by omega))
    have heq : 2 + (2 * k + q) = 2 * (k + 1) + q := by omega
    simpa only [heq] using h

theorem PolarizationData.PolarizedAbelianWithFullLevel.graphBundle_uniform_power_consecutive_sections_factor (m : ℕ) (hm : 0 < m) :
    Section.FactorizationSpans.SectionFactorizationSpan (Line.Bundles.structureModule A.abelian.scheme.left)
      ((A.graphBundle.tensorPower (2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ)).tensorPower m).sheaf
      ((A.graphBundle.tensorPower (2 * Graph.EmbeddingNumerics.graphSquareSectionRank g δ)).tensorPower (m + 1)).sheaf := by
  let r := Graph.EmbeddingNumerics.graphSquareSectionRank g δ
  have hq : 2 * r - 1 ≤ m * (2 * r) := by
    have hmul := Nat.mul_le_mul_right (2 * r) (Nat.succ_le_of_lt hm)
    omega
  have h := A.graphBundle_even_steps_sections_factor hg hδ hN hNk (m * (2 * r)) hq r
  have heq : 2 * r + m * (2 * r) = (m + 1) * (2 * r) := by ring
  rw [heq] at h
  exact (h.sourceIso (A.graphBundle.tensorPowerComposeIso m (2 * r))).targetIso
    (A.graphBundle.tensorPowerComposeIso (m + 1) (2 * r))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
