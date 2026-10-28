import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchDimensionBounds
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCoefficientContext
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPredicate

namespace OAI.Algorithms

/-! Attach the arithmetic envelope to the actual encoded search cost. -/

namespace SubexponentialSAT.Subexp.BlockSearchCostEnvelope

open BlockSearchPredicate

/-- Only the alphabet cardinality is used by the cost proof. Its order may
be the reversed order emitted by the actual scalar formatter. -/
theorem cost_le_expression (p : ℕ) [Fact p.Prime] (alphabet : List (ZMod p))
    (hcard : alphabet.length = p) (m N : ℕ) :
    BlockSearchExecution.cost (scalarCode p) alphabet N
      (BlockCoefficientProgram.coefficientCost p m N) ≤
        BlockSearchArithmetic.costExpression p m N (MatrixWordEncoding.width p) := by
  have hA : 1 ≤ alphabet.length := by
    rw [hcard]
    exact (show Nat.Prime p from Fact.out).one_lt.le
  have h := BlockSearchBounds.cost_le (scalarCode p) alphabet hA N
    (BlockCoefficientProgram.coefficientCost p m N)
  simpa only [BlockSearchArithmetic.costExpression, BlockSearchArithmetic.searchExpression,
    BlockSearchArithmetic.coefficientExpression, BlockSearchExecution.searchBound,
    BlockCoefficientProgram.coefficientCost, hcard, scalarCode,
    BlockSearchProgram.framedCode, MatrixWordEncoding.code] using h

theorem cost_le_two_pow (p : ℕ) [Fact p.Prime] (alphabet : List (ZMod p))
    (hcard : alphabet.length = p) (m N U : ℕ)
    (hpU : p ≤ U) (hNU : N ≤ U) (hm : m ≤ U ^ 2)
    (hB : MatrixWordEncoding.width p ≤ U) :
    BlockSearchExecution.cost (scalarCode p) alphabet N
      (BlockCoefficientProgram.coefficientCost p m N) ≤
        2 ^ (1000000 * (U + 1) ^ 10) :=
  (cost_le_expression p alphabet hcard m N).trans
    (BlockSearchArithmetic.costExpression_le_two_pow_global p m N U (MatrixWordEncoding.width p)
      (show Nat.Prime p from Fact.out).one_lt.le hpU hNU hm hB)

end SubexponentialSAT.Subexp.BlockSearchCostEnvelope

end OAI.Algorithms
