import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseProduct
import OAI.Algorithms.SubexponentialSAT.SubexpDenseArithmetic
import OAI.Algorithms.SubexponentialSAT.SubexpDenseParameters

namespace OAI.Algorithms

/-! The actual dense multiplication budget is a fixed-degree polynomial
in the physical word/key widths and the three input/output list lengths. -/

namespace SubexponentialSAT.SubexpDenseProgram.Product

theorem denseEnvelope_le (B I P Q S N : ℕ) (hP : P ≤ N) (hQ : Q ≤ N) (hS : S ≤ N) :
    denseEnvelope B I P Q S ≤ 2000000 * (B + I + 1)^3 * (N + 1)^3 := by
  simpa only [denseEnvelope, recordBits, outerBudget, rowBudget, innerBudget, pairBudget,
    projectionEnvelope, Projection.scanFactor, SubexpFlatAdd.wordCost,
    SubexpDenseArithmetic.formula] using SubexpDenseArithmetic.formula_le B I P Q S N hP hQ hS

open SymbolicCost SubexpSymbolicCost SubexpLiftRing SubexpQuarticRing
open SubexpQuarticFlatMul SubexpDenseSerialization SubexpDenseParameters

/-- This uses the measured multiplication-time bound and the actual retained
key invariant, without a supplied total-cost or execution premise. -/
theorem multiplicationTime_le_polynomial (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D + 1)) (t : QuarticCode p D)
    (P Q : CoeffList D (QuarticCode p D)) (slots : List (RawIndex D)) (N : ℕ)
    (hP : ∀ a ∈ P, Retained D a.1) (hQ : ∀ b ∈ Q, Retained D b.1)
    (hslots : ∀ a ∈ slots, Retained D a)
    (hPN : P.length ≤ N) (hQN : Q.length ≤ N) (hSN : slots.length ≤ N) :
    multiplicationTime p D M t P Q slots ≤
      2000000 * (baseWidth p (D + 1) + indexBits D + 1)^3 * (N + 1)^3 :=
  (multiplicationTime_le_envelope p D M t P Q slots hP hQ hslots).trans
    (denseEnvelope_le _ _ _ _ _ N hPN hQN hSN)

theorem multiplicationTime_le_uniform (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D + 1)) (t : QuarticCode p D)
    (P Q : CoeffList D (QuarticCode p D)) (slots : List (RawIndex D))
    (hP : ∀ a ∈ P, Retained D a.1) (hQ : ∀ b ∈ Q, Retained D b.1)
    (hslots : ∀ a ∈ slots, Retained D a)
    (hPN : P.length ≤ slotCount D) (hQN : Q.length ≤ slotCount D)
    (hSN : slots.length ≤ slotCount D) :
    multiplicationTime p D M t P Q slots ≤
      1024000000 * (parameterSize D 4 (Nat.log 2 p + 1))^12 * (monomialCount D)^4 := by
  apply (multiplicationTime_le_polynomial p D M t P Q slots (slotCount D)
    hP hQ hslots hPN hQN hSN).trans
  simpa using polynomial_le_uniform 2000000 p D

end SubexponentialSAT.SubexpDenseProgram.Product

end OAI.Algorithms
