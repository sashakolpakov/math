import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseMultiplication
import OAI.Algorithms.SubexponentialSAT.SubexpDenseProductBounds

namespace OAI.Algorithms

/-! Polynomial cost of the complete dense multiplication service, including
the actual operand parser, query copies, result framing, and cleanup. -/

namespace SubexponentialSAT.SubexpDenseMultiplication

theorem envelope_le (B I P Q S N : ℕ) (hP : P ≤ N) (hQ : Q ≤ N) (hS : S ≤ N) :
    envelope B I P Q S ≤ 3000000 * (B + I + 1)^3 * (N + 1)^3 := by
  let X := B + I + 1
  let Y := N + 1
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hY : 1 ≤ Y := by dsimp [Y]; omega
  have hrecord : SubexpDenseProgram.Product.recordBits B I ≤ 20 * X := by
    dsimp [SubexpDenseProgram.Product.recordBits, X]
    omega
  have hencoded (count : ℕ) (hc : count ≤ N) :
      1 + SubexpDenseProgram.Product.recordBits B I * count ≤ 21 * X * Y := by
    have h := Nat.mul_le_mul hrecord hc
    dsimp [Y]
    nlinarith [Nat.zero_le (X * N)]
  have hquery : 1 + (2 * I + 2) * S ≤ 3 * X * Y := by
    have hi : 2 * I + 2 ≤ 2 * X := by dsimp [X]; omega
    have h := Nat.mul_le_mul hi hS
    dsimp [Y]
    nlinarith [Nat.zero_le (X * N)]
  have hleft := hencoded P hP
  have hright := hencoded Q hQ
  have hout := hencoded S hS
  have hXY : 1 ≤ X * Y := by simpa using Nat.mul_le_mul hX hY
  have hX3 : X ≤ X^3 := by
    simpa using (Nat.pow_le_pow_right hX (show 1 ≤ 3 by decide))
  have hY3 : Y ≤ Y^3 := by
    simpa using (Nat.pow_le_pow_right hY (show 1 ≤ 3 by decide))
  have hxy3 := Nat.mul_le_mul hX3 hY3
  have hcore := SubexpDenseProgram.Product.denseEnvelope_le B I P Q S N hP hQ hS
  change SubexpDenseProgram.Product.denseEnvelope B I P Q S ≤
    2000000 * X^3 * Y^3 at hcore
  have hoverhead :
      11 * ((1 + SubexpDenseProgram.Product.recordBits B I * P) +
        (1 + SubexpDenseProgram.Product.recordBits B I * Q)) +
        7 * (1 + (2 * I + 2) * S) +
        8 * (1 + SubexpDenseProgram.Product.recordBits B I * S) + 57 ≤
      708 * (X * Y) := by nlinarith
  have hlarge : 708 * (X * Y) ≤ 708 * (X^3 * Y^3) := Nat.mul_le_mul_left 708 hxy3
  change envelope B I P Q S ≤ 3000000 * X^3 * Y^3
  unfold envelope
  nlinarith [Nat.zero_le (X^3 * Y^3)]

open SymbolicCost SubexpSymbolicCost SubexpLiftRing SubexpQuarticRing
open SubexpQuarticFlatMul SubexpDenseSerialization

/-- The full service bound is obtained from actual encoded input and result
sizes; the retained-list invariant is the only structural input condition. -/
theorem bound_le_polynomial (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D + 1)) (t z o : QuarticCode p D)
    (slots : List (RawIndex D)) (P Q : CoeffList D (QuarticCode p D)) (N : ℕ)
    (hP : ∀ a ∈ P, Retained D a.1) (hQ : ∀ b ∈ Q, Retained D b.1)
    (hslots : ∀ a ∈ slots, Retained D a)
    (hPN : P.length ≤ N) (hQN : Q.length ≤ N) (hSN : slots.length ≤ N) :
    bound p D M t z o slots P Q ≤
      3000000 * (baseWidth p (D + 1) + indexBits D + 1)^3 * (N + 1)^3 :=
  (bound_le_envelope p D M t z o slots P Q hP hQ hslots).trans
    (envelope_le _ _ _ _ _ N hPN hQN hSN)

theorem bound_le_uniform (p D : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p (D + 1)) (t z o : QuarticCode p D)
    (slots : List (RawIndex D)) (P Q : CoeffList D (QuarticCode p D))
    (hP : ∀ a ∈ P, Retained D a.1) (hQ : ∀ b ∈ Q, Retained D b.1)
    (hslots : ∀ a ∈ slots, Retained D a)
    (hPN : P.length ≤ slotCount D) (hQN : Q.length ≤ slotCount D)
    (hSN : slots.length ≤ slotCount D) :
    bound p D M t z o slots P Q ≤
      1536000000 * (parameterSize D 4 (Nat.log 2 p + 1))^12 * (monomialCount D)^4 := by
  apply (bound_le_polynomial p D M t z o slots P Q (slotCount D)
    hP hQ hslots hPN hQN hSN).trans
  simpa using SubexpDenseParameters.polynomial_le_uniform 3000000 p D

end SubexponentialSAT.SubexpDenseMultiplication

end OAI.Algorithms
