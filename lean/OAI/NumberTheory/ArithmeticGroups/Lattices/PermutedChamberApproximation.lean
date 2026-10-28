import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.DifferenceConstraints
import OAI.NumberTheory.ArithmeticGroups.Lattices.AdjacentWeightBounds

/-! # Permuted Chamber Approximation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.PermutedChamberApproximation.Construction

noncomputable section

/-! Simultaneous bounds in two permutation chambers are a bounded
distance from their exact intersection. -/

open scoped Classical

theorem permuted_chamber_bounded_approximation {n : ℕ} (σ : Equiv.Perm (Fin n))
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : Fin n → ℝ,
      (∀ i j, i.val + 1 = j.val → x i - x j ≤ t) →
      (∀ i j, i.val + 1 = j.val → x (σ i) - x (σ j) ≤ t) →
      ∃ y : Fin n → ℝ, Monotone y ∧ Monotone (y ∘ σ) ∧
        ∀ i, 0 ≤ x i - y i ∧ x i - y i ≤ c := by
  let r : Fin n → Fin n → Prop := fun i j => i ≤ j ∨ σ.symm i ≤ σ.symm j
  obtain ⟨c, hc, hb⟩ := Finite.DifferenceConstraints.Construction.finite_difference_constraints_approximation r
    ((n : ℝ) * t) (mul_nonneg (Nat.cast_nonneg _) ht)
  refine ⟨c, hc, fun x hx hxσ => ?_⟩
  have hr : ∀ i j, r i j → x i - x j ≤ (n : ℝ) * t := by
    intro i j hij
    rcases hij with hij | hij
    · exact AdjacentWeightBounds.Construction.adjacent_difference_chain_bound x t ht hx i j hij
    · simpa only [Equiv.apply_symm_apply] using
        AdjacentWeightBounds.Construction.adjacent_difference_chain_bound (fun k => x (σ k)) t ht hxσ (σ.symm i) (σ.symm j) hij
  obtain ⟨y, hy, hxy⟩ := hb x hr
  refine ⟨y, fun i j hij => hy i j (Or.inl hij), ?_, hxy⟩
  intro i j hij
  exact hy (σ i) (σ j) (Or.inr (by simpa only [Equiv.symm_apply_apply] using hij))

theorem monotone_permuted_inversion_equal {n : ℕ} (σ : Equiv.Perm (Fin n))
    (y : Fin n → ℝ) (hy : Monotone y) (hyσ : Monotone (y ∘ σ))
    (i j : Fin n) (hij : i ≤ j) (hσ : σ.symm j ≤ σ.symm i) : y i = y j := by
  apply le_antisymm (hy hij)
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hyσ hσ

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.PermutedChamberApproximation.Construction
