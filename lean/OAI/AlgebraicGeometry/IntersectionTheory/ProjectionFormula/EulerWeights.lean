import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.PageBounds
import Mathlib.Algebra.Ring.NegOnePow

/-! # Euler Weights -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.EulerWeights

/-! Alternating total-degree weights and the finite degree set for the
bounded iterated Tor page. -/

open scoped Classical

def sign (n : ℤ) : ℚ := (n.negOnePow : ℤ)

theorem sign_succ (n : ℤ) : sign (n + 1) = -sign n := by
  simp [sign, Int.negOnePow_succ]

theorem sign_neg_nat (n : ℕ) : sign (-(n : ℤ)) = (-1 : ℚ) ^ n := by
  simp only [sign, Int.negOnePow_neg, Int.coe_negOnePow_natCast, Int.cast_pow, Int.cast_neg, Int.cast_one]

theorem sign_neg_sum (i j : ℕ) : sign (-(i : ℤ) - (j : ℤ)) = (-1 : ℚ) ^ (i + j) := by
  have h : -(i : ℤ) - (j : ℤ) = -((i + j : ℕ) : ℤ) := by omega
  rw [h, sign_neg_nat]

theorem opposite (r : ℤ) (pq pq' : ℤ × ℤ)
    (h : (ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)).Rel pq pq') :
    sign (pq.1 + pq.2) + sign (pq'.1 + pq'.2) = 0 := by
  change pq + (r, 1 - r) = pq' at h
  have hp := congrArg Prod.fst h
  have hq := congrArg Prod.snd h
  dsimp at hp hq
  have he : pq'.1 + pq'.2 = (pq.1 + pq.2) + 1 := by omega
  rw [he, sign_succ, add_neg_cancel]

def degrees (c : ℕ) : Finset ℤ := (Finset.range (c + 1)).image (fun i : ℕ => -(i : ℤ))

theorem mem_degrees (c : ℕ) (n : ℤ) (hl : -(c : ℤ) ≤ n) (hu : n ≤ 0) : n ∈ degrees c := by
  exact Finset.mem_image.mpr ⟨(-n).toNat, Finset.mem_range.mpr (by omega), by omega⟩

theorem support_degrees (a b : ℕ) (pq : ℤ × ℤ) (h : pq ∈ Tensor.PageBounds.support a b) :
    pq.1 + pq.2 ∈ degrees (a + b) := by
  have hs := (Tensor.PageBounds.mem_support a b pq.1 pq.2).mp h
  apply mem_degrees <;> omega

theorem support_strip (a b : ℕ) (pq : ℤ × ℤ) (h : pq ∈ Tensor.PageBounds.support a b) :
    0 ≤ pq.2 + 1 ∧ pq.2 + 1 ≤ (a : ℤ) := by
  have hs := (Tensor.PageBounds.mem_support a b pq.1 pq.2).mp h
  exact ⟨hs.1, hs.2.1⟩

theorem position_injective : Function.Injective
    (fun ij : ℕ × ℕ => (1 - 2 * (ij.1 : ℤ) - (ij.2 : ℤ), (ij.1 : ℤ) - 1)) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  have hp := congrArg Prod.fst h
  have hq := congrArg Prod.snd h
  dsimp at hp hq
  apply Prod.ext <;> dsimp <;> omega

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.EulerWeights
