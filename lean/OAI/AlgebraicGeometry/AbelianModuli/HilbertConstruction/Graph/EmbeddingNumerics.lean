import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.NormNum

/-! # Embedding Numerics -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics

/-! The fixed ranks and degrees of the graph embeddings. -/

open scoped BigOperators

def graphSquareSectionRank (g : ℕ) (δ : Fin g → ℕ) : ℕ :=
  (2 : ℕ) ^ g * (∏ i, δ i) * 2 ^ g

theorem graphSquareSectionRank_pos (g : ℕ) (δ : Fin g → ℕ) (hδ : ∀ i, 0 < δ i) :
    0 < graphSquareSectionRank g δ := by
  exact Nat.mul_pos (Nat.mul_pos (pow_pos (by decide) g)
    (Finset.prod_pos (fun i _ => hδ i))) (pow_pos (by decide) g)

theorem graphSquareSectionRank_eq (g : ℕ) (δ : Fin g → ℕ) :
    graphSquareSectionRank g δ = (4 : ℕ) ^ g * ∏ i, δ i := by
  dsimp [graphSquareSectionRank]
  calc
    _ = ((2 : ℕ) ^ g * 2 ^ g) * ∏ i, δ i := by ac_rfl
    _ = (4 : ℕ) ^ g * ∏ i, δ i := by rw [← mul_pow]; norm_num

def graphUniformEmbeddingDegree (g : ℕ) (δ : Fin g → ℕ) : ℕ :=
  2 * graphSquareSectionRank g δ

def graphUniformEmbeddingSectionRank (g : ℕ) (δ : Fin g → ℕ) : ℕ :=
  (2 : ℕ) ^ g * (∏ i, δ i) * graphUniformEmbeddingDegree g δ ^ g

theorem graphUniformEmbeddingDegree_pos (g : ℕ) (δ : Fin g → ℕ) (hδ : ∀ i, 0 < δ i) :
    0 < graphUniformEmbeddingDegree g δ :=
  Nat.mul_pos (by decide) (graphSquareSectionRank_pos g δ hδ)

theorem graphUniformEmbeddingSectionRank_pos (g : ℕ) (δ : Fin g → ℕ) (hδ : ∀ i, 0 < δ i) :
    0 < graphUniformEmbeddingSectionRank g δ :=
  Nat.mul_pos (Nat.mul_pos (pow_pos (by decide) g) (Finset.prod_pos (fun i _ => hδ i)))
    (pow_pos (graphUniformEmbeddingDegree_pos g δ hδ) g)

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics
