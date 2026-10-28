import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchArithmetic

namespace OAI.Algorithms

/-! Distinguish a local matrix's column count from its universal block bound. -/

namespace SubexponentialSAT.Subexp.BlockSearchArithmetic

theorem costExpression_mono_columns (p m c U B : ℕ) (hp : 1 ≤ p) (hc : c ≤ U) :
    costExpression p m c B ≤ costExpression p m U B := by
  unfold costExpression searchExpression coefficientExpression
  gcongr

/-- Rows need only be bounded by the square of the universal block size U,
not by the square of the possibly smaller local column count c. -/
theorem costExpression_le_global (p m c U B : ℕ) (hp : 1 ≤ p)
    (hc : c ≤ U) (hm : m ≤ U ^ 2) (hB : B ≤ U) :
    costExpression p m c B ≤ 1000000 * (U + 1) ^ 8 * p ^ (U * U + U) :=
  (costExpression_mono_columns p m c U B hp hc).trans
    (costExpression_le p m U B hp hm hB)

theorem costExpression_le_two_pow_global (p m c U B : ℕ) (hp : 1 ≤ p)
    (hpU : p ≤ U) (hc : c ≤ U) (hm : m ≤ U ^ 2) (hB : B ≤ U) :
    costExpression p m c B ≤ 2 ^ (1000000 * (U + 1) ^ 10) :=
  (costExpression_le_global p m c U B hp hc hm hB).trans
    (polynomial_times_search_le_two_pow p U hpU)

end SubexponentialSAT.Subexp.BlockSearchArithmetic

end OAI.Algorithms
