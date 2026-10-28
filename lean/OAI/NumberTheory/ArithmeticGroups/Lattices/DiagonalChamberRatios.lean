import OAI.NumberTheory.ArithmeticGroups.Lattices.StandardSiegelMatrix
import Mathlib.Order.Fin.Basic

/-! # Diagonal Chamber Ratios -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.DiagonalChamberRatios.Construction

noncomputable section

/-! Adjacent diagonal bounds in the lattice-reduction chamber give
uniform bounds for every upper-triangular conjugation ratio. -/

theorem positive_gap_chain_bound {n : ℕ} (d : Fin n → ℝ) (hd : ∀ i, 0 < d i)
    (hstep : ∀ i j, i.val + 1 = j.val → d i ≤ 2 * d j)
    (i j : Fin n) (hij : i ≤ j) : d i ≤ (2 : ℝ) ^ n * d j := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hm : Monotone (fun r : Fin (n + 1) => (2 : ℝ) ^ r.val * d r) := by
      apply Fin.monotone_iff_le_succ.mpr
      intro r
      have he := mul_le_mul_of_nonneg_left (hstep r.castSucc r.succ rfl)
        (pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) r.val)
      simpa only [Fin.val_castSucc, Fin.val_succ, pow_succ, mul_assoc] using he
    calc
      d i ≤ (2 : ℝ) ^ i.val * d i := by
        exact le_mul_of_one_le_left (hd i).le (one_le_pow₀ (by norm_num))
      _ ≤ (2 : ℝ) ^ j.val * d j := hm hij
      _ ≤ (2 : ℝ) ^ (n + 1) * d j :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) j.isLt.le) (hd j).le

theorem positive_gap_chain_ratio {n : ℕ} (d : Fin n → ℝ) (hd : ∀ i, 0 < d i)
    (hstep : ∀ i j, i.val + 1 = j.val → d i ≤ 2 * d j)
    (i j : Fin n) (hij : i ≤ j) : d i / d j ≤ (2 : ℝ) ^ n :=
  (div_le_iff₀ (hd j)).mpr (positive_gap_chain_bound d hd hstep i j hij)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.DiagonalChamberRatios.Construction
