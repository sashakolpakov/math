import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SumHighWeightCount

/-! # Marked Threshold Positive Sum -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MarkedThresholdPositiveSum

noncomputable section

/-! One maximum weight and strict lower bounds on the remaining
weights force a positive total on a basis of the prescribed cardinality. -/
open scoped BigOperators Classical
universe u

theorem markedThreshold_sum_pos {κ : Type u} [Fintype κ]
    (hκ : 2 ≤ Fintype.card κ) (a : κ → ℝ) (j₀ : κ) (M : ℝ) (_hM : 0 < M)
    (hj₀ : a j₀ = M)
    (hrest : ∀ j ≠ j₀, -M < ((Fintype.card κ : ℝ) - 1) * a j) :
    0 < ∑ j, a j := by
  let E := (Finset.univ : Finset κ).erase j₀
  have hcard : E.card = Fintype.card κ - 1 := by simp only [E, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  have hE : E.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
  have hsum := Finset.sum_lt_sum_of_nonempty hE (fun j hj => hrest j (Finset.mem_erase.mp hj).1)
  have hc : (E.card : ℝ) = (Fintype.card κ : ℝ) - 1 := by
    rw [hcard, Nat.cast_sub (by omega : 1 ≤ Fintype.card κ), Nat.cast_one]
  have hjoin := Finset.sum_erase_add (s := (Finset.univ : Finset κ))
    (fun j => ((Fintype.card κ : ℝ) - 1) * a j) (Finset.mem_univ j₀)
  change (∑ j ∈ E, ((Fintype.card κ : ℝ) - 1) * a j) +
    ((Fintype.card κ : ℝ) - 1) * a j₀ = ∑ j, ((Fintype.card κ : ℝ) - 1) * a j at hjoin
  rw [hj₀] at hjoin
  simp only [← Finset.mul_sum] at hjoin hsum
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  rw [hc] at hsum
  have hr : (0 : ℝ) < (Fintype.card κ : ℝ) - 1 := by
    have hh : (2 : ℝ) ≤ (Fintype.card κ : ℝ) := by exact_mod_cast hκ
    linarith
  nlinarith

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MarkedThresholdPositiveSum
