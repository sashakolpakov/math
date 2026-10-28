import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreBounds

namespace OAI.Algorithms

/-!
# Bounds for the actual tuple tables used by packing

These estimates use the concrete framed record encoding and the executable
Cartesian-power recurrence.  The cost bound includes an empty alphabet.
-/

namespace SubexponentialSAT.Subexp.PackingTupleBounds

theorem records_count_le (rows : List (List Bool)) :
    rows.length ≤ (ProgramEncoding.encodeRecords rows).length := by
  have h := Encoding.length_encodeList_lower id rows
  change rows.length + 1 ≤ (ProgramEncoding.encodeRecords rows).length at h
  omega

theorem member_length_le (rows : List (List Bool)) (x : List Bool) (hx : x ∈ rows) :
    x.length ≤ (ProgramEncoding.encodeRecords rows).length := by
  induction rows generalizing x with
  | nil => simp at hx
  | cons y ys ih =>
      have hlen : (ProgramEncoding.encodeRecords (y :: ys)).length =
          2 * y.length + 2 + (ProgramEncoding.encodeRecords ys).length :=
        Encoding.length_encodeList_cons id y ys
      rcases List.mem_cons.mp hx with rfl | ht
      · omega
      · have h := ih x ht
        omega

theorem powerRows_width (alphabet rows : List (List Bool)) (n L W : ℕ)
    (hr : ∀ x ∈ rows, x.length ≤ L)
    (ha : ∀ x ∈ alphabet, x.length ≤ W) :
    ∀ x ∈ TupleProgram.powerRows alphabet n rows, x.length ≤ L + n * W := by
  induction n generalizing rows L with
  | zero => simpa only [TupleProgram.powerRows, Nat.zero_mul, Nat.add_zero] using hr
  | succ n ih =>
      have h := ih (TupleProgram.cartesianOutput rows alphabet) (L + W)
        (PairScoreBounds.cartesian_width rows alphabet L W hr ha)
      intro x hx
      calc
        x.length ≤ L + W + n * W := h x hx
        _ = L + (n + 1) * W := by ring

theorem powerCost_nil_rows (n : ℕ) :
    TupleProgram.powerCost [] n [] = 19 * n + 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [TupleProgram.powerCost, PairScoreBounds.stepCost_eq,
        PairScoreBounds.volume_nil, List.length_nil, TupleProgram.cartesianOutput,
        List.flatMap_nil, List.reverse_nil, ih]
      ring

theorem powerCost_nil_singleton_succ (n : ℕ) :
    TupleProgram.powerCost [] (n + 1) [[]] = 19 * n + 46 := by
  simp only [TupleProgram.powerCost, PairScoreBounds.stepCost_eq,
    PairScoreBounds.volume_cons, PairScoreBounds.volume_nil,
    List.length_cons, List.length_nil, TupleProgram.cartesianOutput,
    List.flatMap_cons, List.flatMap_nil, List.map_nil, List.nil_append,
    List.reverse_nil, powerCost_nil_rows]
  ring

/-- The generated-table bound is valid also when no alphabet record exists.
In that case the first expansion empties the table, and subsequent iterations
have the exact linear cost shown above. -/
theorem generated_powerCost_le (alphabet : List (List Bool)) (n W : ℕ)
    (ha : ∀ x ∈ alphabet, x.length ≤ W) :
    TupleProgram.powerCost alphabet n [[]] ≤
      800 * (n + 1) * (alphabet.length ^ n + 1) * ((n + 1) * W + 1) := by
  cases alphabet with
  | nil =>
      cases n with
      | zero =>
          simp only [TupleProgram.powerCost, List.length_nil, pow_zero,
            Nat.zero_add, Nat.one_mul, Nat.mul_one]
          omega
      | succ n =>
          rw [powerCost_nil_singleton_succ]
          simp only [List.length_nil, zero_pow (Nat.succ_ne_zero n),
            Nat.zero_add, Nat.mul_one]
          calc
            19 * n + 46 ≤ 800 * (n + 1 + 1) := by omega
            _ = 800 * (n + 1 + 1) * 1 := by ring
            _ ≤ 800 * (n + 1 + 1) * ((n + 1 + 1) * W + 1) :=
              Nat.mul_le_mul_left _ (by omega)
  | cons a alphabet =>
      have h := PairScoreBounds.generated_powerCost_le (a :: alphabet) n W (by simp) ha
      exact h.trans (Nat.mul_le_mul_right _
        (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)))

end SubexponentialSAT.Subexp.PackingTupleBounds

end OAI.Algorithms
