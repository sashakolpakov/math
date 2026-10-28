import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval

namespace OAI.Algorithms

/-! Integer arithmetic for the exact centered interval used by the layout. -/

namespace SubexponentialSAT.SubexpIntervalStart

/-- This is computed using two truncated predecessors, products, truncated
subtraction, and natural division. -/
def value (r Q R : ℕ) : ℕ := ((Q - 1) * (r - 1) - R * r) / (2 * r)

theorem value_eq_intervalStart (r Q R : ℕ) (hr : 0 < r) :
    value r Q R = Subexp.TailInterval.intervalStart r Q R := by
  have hr1 : 1 ≤ r := hr
  have hr0 : (r : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)
  have hcommon : ((Q - 1 : ℕ) : ℚ) * (((r : ℚ) - 1) / (2 * r)) - (R : ℚ) / 2 =
      ((((Q - 1) * (r - 1) : ℕ) : ℚ) - ((R * r : ℕ) : ℚ)) / ((2 * r : ℕ) : ℚ) := by
    simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hr1, Nat.cast_one]
    field_simp
  unfold Subexp.TailInterval.intervalStart Subexp.TailInterval.centeredStart
    Subexp.TailInterval.mean SubexpSwapMultiplicity.negativeProbability
  rw [hcommon, Nat.floor_div_natCast, Nat.floor_sub_natCast, Nat.floor_natCast]
  rfl

end SubexponentialSAT.SubexpIntervalStart

end OAI.Algorithms
