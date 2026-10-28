import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Field.Rat

/-! # Euler Index -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.EulerIndex

/-! Reindexing a finitely supported spectral-page sum by total degree
and filtration index. -/

open scoped BigOperators Classical

def position (ni : ℤ × ℕ) : ℤ × ℤ := (ni.1 - ((ni.2 : ℤ) - 1), (ni.2 : ℤ) - 1)

theorem position_injective : Function.Injective position := by
  rintro ⟨n, i⟩ ⟨m, j⟩ h
  have hp := congrArg Prod.fst h
  have hq := congrArg Prod.snd h
  dsimp [position] at hp hq
  apply Prod.ext <;> dsimp <;> omega

theorem degree_position (ni : ℤ × ℕ) : (position ni).1 + (position ni).2 = ni.1 := by
  exact sub_add_cancel _ _

theorem sum_by_degree (F : Finset (ℤ × ℤ)) (N : Finset ℤ) (a : ℕ)
    (hdegree : ∀ pq ∈ F, pq.1 + pq.2 ∈ N)
    (hstrip : ∀ pq ∈ F, 0 ≤ pq.2 + 1 ∧ pq.2 + 1 ≤ (a : ℤ))
    (f : ℤ × ℤ → ℚ) (hout : ∀ pq, pq ∉ F → f pq = 0) (w : ℤ → ℚ) :
    (∑ n ∈ N, w n * ∑ i ∈ Finset.range (a + 1), f (position (n, i))) =
      ∑ pq ∈ F, w (pq.1 + pq.2) * f pq := by
  let G := (N.product (Finset.range (a + 1))).image position
  have hsub : F ⊆ G := by
    intro pq hpq
    have hs := hstrip pq hpq
    refine Finset.mem_image.mpr ⟨(pq.1 + pq.2, (pq.2 + 1).toNat),
      Finset.mem_product.mpr ⟨hdegree pq hpq, Finset.mem_range.mpr (by omega)⟩, ?_⟩
    apply Prod.ext <;> dsimp [position] <;> omega
  calc
    _ = ∑ ni ∈ N.product (Finset.range (a + 1)), w ni.1 * f (position ni) := by
      rw [Finset.product_eq_sprod, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro n _
      rw [Finset.mul_sum]
    _ = ∑ pq ∈ G, w (pq.1 + pq.2) * f pq := by
      rw [Finset.sum_image (fun _ _ _ _ h => position_injective h)]
      apply Finset.sum_congr rfl
      intro ni _
      rw [degree_position]
    _ = _ := (Finset.sum_subset hsub (fun pq _ hpq => by rw [hout pq hpq, mul_zero])).symm

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Tensor.EulerIndex
