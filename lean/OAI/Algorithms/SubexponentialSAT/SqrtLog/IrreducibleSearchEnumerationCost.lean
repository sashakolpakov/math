import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchEnumeration
import OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreBounds

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchEnumeration

open SubexpOrderedTupleData Subexp.PairScoreBounds SubexpEnumerationPayload

private theorem cartesian_width (rows alphabet : List (List Bool)) (L W : ℕ)
    (hr : ∀ row ∈ rows, row.length ≤ L)
    (ha : ∀ row ∈ alphabet, row.length ≤ W) :
    ∀ row ∈ orderedCartesian rows alphabet, row.length ≤ L + W := by
  rw [orderedCartesian_eq_reverse]
  simpa only [List.mem_reverse] using
    Subexp.PairScoreBounds.cartesian_width rows alphabet L W hr ha

private theorem ordered_step_le (rows alphabet : List (List Bool)) (L W : ℕ)
    (hr : ∀ row ∈ rows, row.length ≤ L)
    (ha : ∀ row ∈ alphabet, row.length ≤ W) :
    SubexpOrderedTupleStep.stepCost rows alphabet + 2 ≤
      200 * (rows.length + 1) * (alphabet.length + 1) * (L + W + 1) := by
  have hv := volume_le rows L hr
  have hu := volume_le alphabet W ha
  rw [SubexpOrderedTupleProgram.stepCost_eq]
  change 17 + (32 * alphabet.length + 8) * volume rows +
    (45 * volume alphabet + 56 * alphabet.length + 25) * rows.length + 2 ≤ _
  calc
    _ = 19 + (32 * alphabet.length + 8) * volume rows +
        (45 * volume alphabet + 56 * alphabet.length + 25) * rows.length := by ring
    _ ≤ 19 + (32 * alphabet.length + 8) * (rows.length * L) +
        (45 * (alphabet.length * W) + 56 * alphabet.length + 25) * rows.length := by
      gcongr
    _ ≤ _ + (168 * rows.length * alphabet.length * L + 155 * rows.length * alphabet.length * W +
        144 * rows.length * alphabet.length + 192 * rows.length * L + 200 * rows.length * W +
        175 * rows.length + 200 * alphabet.length * L + 200 * alphabet.length * W +
        200 * alphabet.length + 200 * L + 200 * W + 181) := Nat.le_add_right _ _
    _ = _ := by ring

theorem powerCost_le (alphabet rows : List (List Bool)) (n L W : ℕ)
    (hA : 1 ≤ alphabet.length)
    (hr : ∀ row ∈ rows, row.length ≤ L)
    (ha : ∀ row ∈ alphabet, row.length ≤ W) :
    powerCost alphabet n rows ≤
      400 * (n + 1) * (rows.length + 1) * alphabet.length ^ n * (L + n * W + W + 1) := by
  induction n generalizing rows L with
  | zero =>
    simp only [powerCost, Nat.zero_add, pow_zero, Nat.mul_one, Nat.zero_mul]
    nlinarith
  | succ n ih =>
    have hi := ih (orderedCartesian rows alphabet) (L + W)
      (cartesian_width rows alphabet L W hr ha)
    rw [orderedCartesian_length] at hi
    have hs := ordered_step_le rows alphabet L W hr ha
    have hA' : alphabet.length + 1 ≤ 2 * alphabet.length := by omega
    have hs' : SubexpOrderedTupleStep.stepCost rows alphabet + 2 ≤
        400 * (rows.length + 1) * alphabet.length * (L + W + 1) := by
      calc
        _ ≤ 200 * (rows.length + 1) * (alphabet.length + 1) * (L + W + 1) := hs
        _ ≤ 200 * (rows.length + 1) * (2 * alphabet.length) * (L + W + 1) := by gcongr
        _ = _ := by ring
    have hpow : alphabet.length ≤ alphabet.length ^ (n + 1) := by
      simpa only [pow_one] using pow_le_pow_right₀ hA (show 1 ≤ n + 1 by omega)
    have hwidth : L + W + 1 ≤ L + (n + 1) * W + W + 1 := by nlinarith
    have hstep : SubexpOrderedTupleStep.stepCost rows alphabet + 2 ≤
        400 * (rows.length + 1) * alphabet.length ^ (n + 1) *
          (L + (n + 1) * W + W + 1) := by
      exact hs'.trans (by gcongr)
    have hrA : rows.length * alphabet.length + 1 ≤ (rows.length + 1) * alphabet.length := by
      nlinarith
    have hrec : powerCost alphabet n (orderedCartesian rows alphabet) ≤
        400 * (n + 1) * (rows.length + 1) * alphabet.length ^ (n + 1) *
          (L + (n + 1) * W + W + 1) := by
      calc
        _ ≤ 400 * (n + 1) * (rows.length * alphabet.length + 1) * alphabet.length ^ n *
            (L + W + n * W + W + 1) := hi
        _ ≤ 400 * (n + 1) * ((rows.length + 1) * alphabet.length) * alphabet.length ^ n *
            (L + W + n * W + W + 1) := by gcongr
        _ = _ := by rw [pow_succ]; ring
    rw [powerCost]
    have hsum := Nat.add_le_add hstep hrec
    nlinarith

theorem generated_powerCost_le (alphabet : List (List Bool)) (n W : ℕ)
    (hA : 1 ≤ alphabet.length) (ha : ∀ row ∈ alphabet, row.length ≤ W) :
    powerCost alphabet n [[]] ≤
      800 * (n + 1) * alphabet.length ^ n * ((n + 1) * W + 1) := by
  have h := powerCost_le alphabet [[]] n 0 W hA (by simp) ha
  calc
    _ ≤ 400 * (n + 1) * ([[]] : List (List Bool)).length.succ * alphabet.length ^ n *
        (0 + n * W + W + 1) := h
    _ = _ := by simp only [List.length_cons, List.length_nil, Nat.succ_eq_add_one]; ring

@[simp] theorem alphabet_length : alphabet.length = 3 := by
  simp [alphabet, QuarticSearch.length_elements]

theorem cost_le (d : ℕ) : cost d ≤
    800 * (d + 1) * 3 ^ d * ((d + 1) * scalarWidth 3 + 1) + 9 := by
  have h := generated_powerCost_le alphabet d (scalarWidth 3)
    (by simp) (by
      intro row hrow
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hrow
      exact le_of_eq ((scalarCode 3).length_block x))
  simpa only [cost, alphabet_length] using Nat.add_le_add_right h 9

end SubexponentialSAT.SqrtLog.IrreducibleSearchEnumeration

end OAI.Algorithms
