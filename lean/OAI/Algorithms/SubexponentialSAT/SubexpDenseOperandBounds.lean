import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpDenseOperands
import OAI.Algorithms.SubexponentialSAT.SubexpDenseProjectionBounds

namespace OAI.Algorithms

/-! Uniform bounds for the actual LOAD and ADD services. LOAD keeps the
actual raw serialized length, including non-retained keys and duplicates. -/

namespace SubexponentialSAT.SubexpDenseOperands

open SymbolicCost SubexpSymbolicCost SubexpLiftRing SubexpQuarticRing
open SubexpDenseSerialization SubexpDenseProjectionBounds

variable (p D : ℕ) [Fact p.Prime]
  (M : SubexpPreparedQuartic.Modulus p (D + 1)) (t z o : QuarticCode p D)
  (slots : List (RawIndex D))

theorem loadBound_le_envelope (P : CoeffList D (QuarticCode p D))
    (hs : ∀ a ∈ slots, Retained D a) :
    loadBound p D M t z o slots P ≤
      loadEnvelope (baseWidth p (D + 1)) (indexBits D) slots.length
        (encodeFixedQuarticCoefficients p D P).length := by
  have hc := projectionTime_le p D M P slots hs
  have hq := queryBytes_length D slots hs
  have ho := project_serialized_length p D (preparedProgram p D M t z o) slots hs P
  unfold loadBound loadEnvelope
  omega

theorem addBound_le_envelope (P Q : CoeffList D (QuarticCode p D))
    (hs : ∀ a ∈ slots, Retained D a) :
    addBound p D M t z o slots P Q ≤
      addEnvelope (baseWidth p (D + 1)) (indexBits D) slots.length
        (encodeFixedQuarticCoefficients p D P).length
        (encodeFixedQuarticCoefficients p D Q).length := by
  have hc := additionTime_le p D M P Q slots hs
  have hq := queryBytes_length D slots hs
  have ho := add_serialized_length p D (preparedProgram p D M t z o) slots hs P Q
  have he (B I N L R : ℕ) :
      addEnvelope B I N L R =
        4 + N * (6 * I + SubexpDenseProgram.Projection.scanFactor B I * (L + R + 2) + 7) +
          11 * (L + R) + 7 * (1 + (2 * I + 2) * N) +
          8 * (1 + recordBits B I * N) + 57 := by
    unfold addEnvelope loadEnvelope
    ring
  rw [he]
  unfold addBound
  omega

/-- Parsing a raw literal is charged by its actual byte length. There is
no retained-key or duplicate-freedom hypothesis on that input. -/
theorem loadBound_le_polynomial (P : CoeffList D (QuarticCode p D))
    (hs : ∀ a ∈ slots, Retained D a) :
    loadBound p D M t z o slots P ≤
      40000 * (baseWidth p (D + 1) + indexBits D + 1)^2 *
        (slots.length + 1) * ((encodeFixedQuarticCoefficients p D P).length + 1) :=
  (loadBound_le_envelope p D M t z o slots P hs).trans (loadEnvelope_le _ _ _ _)

theorem addBound_le_polynomial (P Q : CoeffList D (QuarticCode p D)) (N : ℕ)
    (hP : ∀ a ∈ P, Retained D a.1) (hQ : ∀ a ∈ Q, Retained D a.1)
    (hs : ∀ a ∈ slots, Retained D a)
    (hPN : P.length ≤ N) (hQN : Q.length ≤ N) (hSN : slots.length ≤ N) :
    addBound p D M t z o slots P Q ≤
      2000000 * (baseWidth p (D + 1) + indexBits D + 1)^3 * (N + 1)^3 := by
  have hl : (encodeFixedQuarticCoefficients p D P).length ≤
      1 + recordBits (baseWidth p (D + 1)) (indexBits D) * N := by
    rw [retained_serialized_length p D P hP]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hPN) 1
  have hr : (encodeFixedQuarticCoefficients p D Q).length ≤
      1 + recordBits (baseWidth p (D + 1)) (indexBits D) * N := by
    rw [retained_serialized_length p D Q hQ]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hQN) 1
  apply (addBound_le_envelope p D M t z o slots P Q hs).trans
  calc
    _ ≤ addEnvelope (baseWidth p (D + 1)) (indexBits D) N
        (encodeFixedQuarticCoefficients p D P).length
        (encodeFixedQuarticCoefficients p D Q).length := by
      unfold addEnvelope loadEnvelope
      gcongr
    _ ≤ _ := addEnvelope_le _ _ _ _ _ hl hr

theorem addBound_le_uniform (P Q : CoeffList D (QuarticCode p D))
    (hP : ∀ a ∈ P, Retained D a.1) (hQ : ∀ a ∈ Q, Retained D a.1)
    (hs : ∀ a ∈ slots, Retained D a)
    (hPN : P.length ≤ slotCount D) (hQN : Q.length ≤ slotCount D)
    (hSN : slots.length ≤ slotCount D) :
    addBound p D M t z o slots P Q ≤
      1024000000 * (parameterSize D 4 (Nat.log 2 p + 1))^12 * (monomialCount D)^4 := by
  apply (addBound_le_polynomial p D M t z o slots P Q (slotCount D)
    hP hQ hs hPN hQN hSN).trans
  simpa using SubexpDenseParameters.polynomial_le_uniform 2000000 p D

/-- Uniform stored-parameter cost, retaining the real serialized literal
length as a multiplicative factor for the builder to discharge. -/
theorem loadBound_le_uniform (P : CoeffList D (QuarticCode p D))
    (hs : ∀ a ∈ slots, Retained D a) (hSN : slots.length ≤ slotCount D) :
    loadBound p D M t z o slots P ≤
      1280000 * (parameterSize D 4 (Nat.log 2 p + 1))^6 * monomialCount D *
        ((encodeFixedQuarticCoefficients p D P).length + 1) := by
  let X := parameterSize D 4 (Nat.log 2 p + 1)
  have hX : 1 ≤ X := by dsimp [X,parameterSize]; omega
  have hX2 : 1 ≤ X^2 := by nlinarith
  have hD : D + 1 ≤ X := by dsimp [X,parameterSize]; omega
  have hb : Nat.log 2 p + 1 ≤ X := by dsimp [X,parameterSize]; omega
  have hB : baseWidth p (D + 1) ≤ X^2 := by
    simpa only [baseWidth,pow_two] using Nat.mul_le_mul hD hb
  have hI : indexBits D ≤ 2 * X^2 := indexBits_degree D 4 (Nat.log 2 p + 1)
  have hW : baseWidth p (D + 1) + indexBits D + 1 ≤ 4 * X^2 := by omega
  have hM : 1 ≤ monomialCount D := Nat.choose_pos (by omega : D ≤ 3 * D + 1)
  have hMX : 1 ≤ monomialCount D * X^2 := by simpa using Nat.mul_le_mul hM hX2
  have hslots : slotCount D ≤ monomialCount D * X^2 := by
    apply Nat.mul_le_mul_left
    simpa only [pow_two] using Nat.mul_le_mul hD ((Nat.le_succ D).trans hD)
  have hN : slots.length + 1 ≤ 2 * (monomialCount D * X^2) := by omega
  apply (loadBound_le_polynomial p D M t z o slots P hs).trans
  calc
    _ ≤ 40000 * (4 * X^2)^2 * (2 * (monomialCount D * X^2)) *
        ((encodeFixedQuarticCoefficients p D P).length + 1) := by gcongr
    _ = _ := by dsimp [X]; ring

end SubexponentialSAT.SubexpDenseOperands

end OAI.Algorithms
