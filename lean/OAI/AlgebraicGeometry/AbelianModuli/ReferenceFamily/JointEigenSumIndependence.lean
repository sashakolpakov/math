import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Algebra.BigOperators.Module

/-! # Joint Eigen Sum Independence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.JointEigenSumIndependence

noncomputable section

/-! Joint character spaces for distinct characters have independent
finite sums. No choice of a common diagonalizing operator is required. -/

open scoped BigOperators

theorem jointEigenvectors_sum_eq_zero
    {k V R I : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : R → V →ₗ[k] V) (χ : I → R → k) (hχ : Function.Injective χ)
    (s : Finset I) (x : I → V)
    (hx : ∀ i ∈ s, ∀ a, ρ a (x i) = χ i a • x i)
    (hz : ∑ i ∈ s, x i = 0) : ∀ i ∈ s, x i = 0 := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty =>
    intro i hi
    exact False.elim (Finset.notMem_empty i hi)
  | @insert i s hi ih =>
    have hrest : ∀ j ∈ s, x j = 0 := by
      intro j hj
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      have hne : ¬ ∀ a, χ j a = χ i a := fun h => hji (hχ (funext h))
      obtain ⟨a, ha⟩ := not_forall.mp hne
      let y : I → V := fun l => (χ l a - χ i a) • x l
      have hy : ∀ l ∈ s, ∀ b, ρ b (y l) = χ l b • y l := by
        intro l hl b
        dsimp only [y]
        rw [map_smul, hx l (Finset.mem_insert_of_mem hl) b, smul_comm]
      have hall : ∑ l ∈ insert i s, y l = 0 := by
        calc
          _ = ρ a (∑ l ∈ insert i s, x l) - χ i a • (∑ l ∈ insert i s, x l) := by
            rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro l hl
            rw [hx l hl a]
            exact sub_smul _ _ _
          _ = 0 := by rw [hz, map_zero, smul_zero, sub_self]
      have hsum : ∑ l ∈ s, y l = 0 := by
        simpa only [Finset.sum_insert hi, y, sub_self, zero_smul, zero_add] using hall
      have hjzero := ih y hy hsum j hj
      have hc : χ j a - χ i a ≠ 0 := sub_ne_zero.mpr ha
      have hinv := congrArg (fun z : V => (χ j a - χ i a)⁻¹ • z) hjzero
      simpa only [y, smul_smul, inv_mul_cancel₀ hc, one_smul, smul_zero] using hinv
    have hfirst : x i = 0 := by
      rw [Finset.sum_insert hi, Finset.sum_eq_zero hrest, add_zero] at hz
      exact hz
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact hfirst
    · exact hrest j hj

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.JointEigenSumIndependence
