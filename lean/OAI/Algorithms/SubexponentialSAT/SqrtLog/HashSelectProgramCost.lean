import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectProgramGenerate

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.Subexp

private theorem sum_lengths_le (rows : Records) (w : ℕ)
    (h : ∀ x ∈ rows, x.length ≤ w) : (rows.map List.length).sum ≤ rows.length * w := by
  induction rows with
  | nil => simp
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith

theorem tupleCost_bound (alphabet : Records) (tuple : List Bool) (b w : ℕ)
    (ha : ∀ x ∈ alphabet, x.length ≤ b) (ht : tuple.length ≤ w) :
    TupleProgram.tupleCost alphabet tuple ≤
      (12 * alphabet.length + 2) * w + 25 * alphabet.length * b + 36 * alphabet.length + 18 := by
  have he := ProgramEncoding.encodeRecords_length_le alphabet b ha
  have hl := sum_lengths_le alphabet b ha
  have hb := RecordPrograms.budget_le_linear
    (fun word => 5 * word.length + 12 * tuple.length + 15) alphabet 5 (12 * w + 15)
    (by intro x _; omega)
  unfold TupleProgram.tupleCost
  nlinarith

theorem cartesian_width_le (alphabet rows : Records) (a b : ℕ)
    (ha : ∀ x ∈ alphabet, x.length ≤ a) (hb : ∀ x ∈ rows, x.length ≤ b) :
    ∀ x ∈ TupleProgram.cartesianOutput rows alphabet, x.length ≤ b + a := by
  intro x hx
  simp only [TupleProgram.cartesianOutput, List.mem_reverse, List.mem_flatMap] at hx
  obtain ⟨row, hr, hx⟩ := hx
  obtain ⟨word, hw, rfl⟩ := List.mem_map.mp hx
  simpa only [List.length_append] using Nat.add_le_add (hb row hr) (ha word hw)

theorem stepCost_bound (alphabet rows : Records) (b w : ℕ)
    (ha : ∀ x ∈ alphabet, x.length ≤ b) (hr : ∀ x ∈ rows, x.length ≤ w) :
    TupleProgram.stepCost rows alphabet ≤
      100 * (rows.length + 1) * (alphabet.length + 1) * (w + b + 1) := by
  have hl := sum_lengths_le rows w hr
  have hb := RecordPrograms.budget_le_linear (TupleProgram.tupleCost alphabet) rows
    0 ((12 * alphabet.length + 2) * w + 25 * alphabet.length * b +
      36 * alphabet.length + 18)
    (by intro x hx; simpa using tupleCost_bound alphabet x b w ha (hr x hx))
  have he := ProgramEncoding.encodeRecords_length_le
    (TupleProgram.cartesianOutput rows alphabet) (w + b) (cartesian_width_le alphabet rows b w ha hr)
  have hc : (TupleProgram.cartesianOutput rows alphabet).length = rows.length * alphabet.length := by
    simp [TupleProgram.cartesianOutput]
  rw [hc] at he
  unfold TupleProgram.stepCost TupleProgram.expansionCost
  nlinarith

/-- Paid enumeration overhead is polynomial in output size, width and depth.
This bound applies to the audited runtime-depth controller, not an unrolled
family of programs. -/
theorem powerCost_bound (alphabet rows : Records) (b w d : ℕ)
    (ha : ∀ x ∈ alphabet, x.length ≤ b) (hr : ∀ x ∈ rows, x.length ≤ w) :
    TupleProgram.powerCost alphabet d rows ≤
      200 * (d + 1) * (rows.length + 1) * (alphabet.length + 1) ^ (d + 1) *
        (w + (d + 1) * b + 1) := by
  induction d generalizing rows w with
  | zero =>
    simp only [TupleProgram.powerCost, Nat.zero_add, Nat.pow_one, Nat.one_mul]
    have h : 0 < (rows.length + 1) * (alphabet.length + 1) * (w + b + 1) := by positivity
    nlinarith
  | succ d ih =>
    let A := alphabet.length
    let R := rows.length
    let W := w + (d + 2) * b + 1
    let S := (R + 1) * (A + 1) ^ (d + 2) * W
    have hc : (TupleProgram.cartesianOutput rows alphabet).length = R * A := by
      simp [TupleProgram.cartesianOutput, R, A]
    have hnext := ih (TupleProgram.cartesianOutput rows alphabet) (w + b)
      (cartesian_width_le alphabet rows b w ha hr)
    have hwidth : w + b + (d + 1) * b + 1 = W := by dsimp [W]; ring
    rw [hc, hwidth] at hnext
    have hRA : R * A + 1 ≤ (R + 1) * (A + 1) := by nlinarith
    have hnext' : TupleProgram.powerCost alphabet d (TupleProgram.cartesianOutput rows alphabet) ≤
        200 * (d + 1) * S := by
      calc
        _ ≤ 200 * (d + 1) * (R * A + 1) * (A + 1) ^ (d + 1) * W := hnext
        _ ≤ 200 * (d + 1) * ((R + 1) * (A + 1)) * (A + 1) ^ (d + 1) * W :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hRA))
        _ = _ := by dsimp [S]; rw [show d + 2 = (d + 1) + 1 by omega, pow_succ]; ring
    have hpow : A + 1 ≤ (A + 1) ^ (d + 2) := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < A + 1) (show 1 ≤ d + 2 by omega)
    have hw : w + b + 1 ≤ W := by dsimp [W]; nlinarith
    have hbase : (R + 1) * (A + 1) * (w + b + 1) ≤ S :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hpow) hw
    have hS : 0 < S := by
      dsimp [S, W]
      positivity
    have hstep := stepCost_bound alphabet rows b w ha hr
    have hstep' : TupleProgram.stepCost rows alphabet + 2 ≤ 200 * S := by
      change TupleProgram.stepCost rows alphabet ≤ 100 * (R + 1) * (A + 1) * (w + b + 1) at hstep
      nlinarith
    calc
      _ = TupleProgram.stepCost rows alphabet +
          TupleProgram.powerCost alphabet d (TupleProgram.cartesianOutput rows alphabet) + 2 := rfl
      _ ≤ 200 * (d + 2) * S := by nlinarith
      _ = _ := by dsimp [S, R, A, W]; ring

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
