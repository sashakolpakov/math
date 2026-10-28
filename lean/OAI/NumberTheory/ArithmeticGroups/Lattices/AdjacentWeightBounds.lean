import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.WeightsAsDifferences
import Mathlib.Order.Fin.Basic

/-! # Adjacent Weight Bounds -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! Adjacent additive weight bounds imply bounds for every positive
intrinsic weight, with a dimension-dependent cutoff. -/

theorem AdjacentWeightBounds.Construction.adjacent_difference_chain_bound {n : ℕ} (x : Fin n → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hstep : ∀ i j, i.val + 1 = j.val → x i - x j ≤ t)
    (i j : Fin n) (hij : i ≤ j) : x i - x j ≤ (n : ℝ) * t := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hm : Monotone (fun r : Fin (n + 1) => x r + (r.val : ℝ) * t) := by
      apply Fin.monotone_iff_le_succ.mpr
      intro r
      have he := hstep r.castSucc r.succ rfl
      simp only [Fin.val_castSucc, Fin.val_succ, Nat.cast_add, Nat.cast_one]
      linarith
    have he := hm hij
    have hi : 0 ≤ (i.val : ℝ) * t := mul_nonneg (Nat.cast_nonneg _) ht
    have hj : (j.val : ℝ) * t ≤ ((n + 1 : ℕ) : ℝ) * t :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr j.isLt.le) ht
    linarith

theorem KillingSplit.Construction.KillingSplitWeightData.chamber_of_adjacent_weight_bounds
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {B : L →L[ℝ] L →L[ℝ] L} (d : KillingSplit.Construction.KillingSplitWeightData B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hd : Antitone (fun i => d.weight i d.regularElement)) (A : d.subspace) (t : ℝ) (ht : 0 ≤ t)
    (hA : ∀ i j, i.val + 1 = j.val → d.weight i A - d.weight j A ≤ t) :
    A ∈ d.truncatedNegativeChamber ((Module.finrank ℝ L : ℝ) * t) := by
  apply d.chamber_of_upper_differences hK hd A
  intro i j hij
  exact AdjacentWeightBounds.Construction.adjacent_difference_chain_bound (fun r => d.weight r A) t ht hA i j hij.le

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
