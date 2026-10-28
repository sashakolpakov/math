import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterExecution
import OAI.Algorithms.SubexponentialSAT.SubexpCRTOuterCostCore

namespace OAI.Algorithms

/-! A single polynomial majorant for the actual complete CRT instruction
bound. The numerical exponent is included explicitly: it is the prepared
Fermat exponent, not an uncharged large-integer operation. -/

namespace SubexponentialSAT.SubexpCRTOuterCost

open SubexpLiftRing

variable (p D : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
theorem middleBudget_eq (Q : ℕ) (exponent : List Bool) :
    SubexpCRTOuterExecution.middleBudget p D Q exponent =
      middleBound (baseWidth p (D + 1)) D Q exponent := rfl

omit [Fact p.Prime] in
theorem commandBudget_eq (Q : ℕ) (exponent : List Bool) :
    SubexpCRTOuterExecution.commandBudget p D Q exponent =
      commandBound (baseWidth p (D + 1)) D Q exponent := rfl

omit [Fact p.Prime] in
theorem middleBudget_le (Q : ℕ) (exponent : List Bool) (W : ℕ)
    (hB : baseWidth p (D + 1) ≤ W) (hD : D ≤ W) (hQ : Q ≤ W)
    (hE : exponent.length ≤ W) (hN : BinaryArithmetic.toNat exponent ≤ W) :
    SubexpCRTOuterExecution.middleBudget p D Q exponent ≤ middleMajorant W := by
  rw [middleBudget_eq]
  exact middleBound_le _ D Q exponent W hB hD hQ hE hN

omit [Fact p.Prime] in
theorem commandBudget_le (Q : ℕ) (exponent : List Bool) (W : ℕ)
    (hB : baseWidth p (D + 1) ≤ W) (hD : D ≤ W) (hQ : Q ≤ W)
    (hE : exponent.length ≤ W) (hN : BinaryArithmetic.toNat exponent ≤ W) :
    SubexpCRTOuterExecution.commandBudget p D Q exponent + 1 ≤ majorant W := by
  rw [commandBudget_eq]
  exact commandBound_le _ D Q exponent W hB hD hQ hE hN

omit [Fact p.Prime] in
theorem commandBudget_le_degree_eight (Q : ℕ) (exponent : List Bool) (W : ℕ)
    (hB : baseWidth p (D + 1) ≤ W) (hD : D ≤ W) (hQ : Q ≤ W)
    (hE : exponent.length ≤ W) (hN : BinaryArithmetic.toNat exponent ≤ W) :
    SubexpCRTOuterExecution.commandBudget p D Q exponent + 1 ≤ 800000000 * (W + 1)^8 :=
  (commandBudget_le p D Q exponent W hB hD hQ hE hN).trans (majorant_le_degree_eight W)

omit [Fact p.Prime] in
theorem commandBudget_le_inputs (Q : ℕ) (exponent : List Bool) :
    SubexpCRTOuterExecution.commandBudget p D Q exponent + 1 ≤
      800000000 * (baseWidth p (D + 1) + D + Q + exponent.length +
        BinaryArithmetic.toNat exponent + 1)^8 := by
  rw [commandBudget_eq]
  exact commandBound_le_inputs _ D Q exponent

end SubexponentialSAT.SubexpCRTOuterCost

end OAI.Algorithms
