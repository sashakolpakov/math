import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PairScoreProgram

namespace OAI.Algorithms

/-!
# Closed bounds for the actual tuple generator and pair scorer

All costs below are the explicit bounds attached to proved executions of the
fixed programs.  The tuple recurrence is bounded from its actual list sizes;
no scalar-operation or callback-cost oracle is assumed.
-/

namespace SubexponentialSAT.Subexp.PairScoreBounds

open BitProgram

def volume (rows : List (List Bool)) : ℕ := (rows.map List.length).sum

@[simp] theorem volume_nil : volume [] = 0 := rfl
@[simp] theorem volume_cons (row : List Bool) (rows : List (List Bool)) :
    volume (row :: rows) = row.length + volume rows := rfl

@[simp] theorem volume_append (xs ys : List (List Bool)) :
    volume (xs ++ ys) = volume xs + volume ys := by simp [volume]

@[simp] theorem volume_reverse (xs : List (List Bool)) :
    volume xs.reverse = volume xs := by simp [volume]

theorem volume_prefix (pref : List Bool) (rows : List (List Bool)) :
    volume (rows.map (fun row => pref ++ row)) = rows.length * pref.length + volume rows := by
  induction rows with
  | nil => simp
  | cons row rows ih => simp only [List.map_cons, volume_cons, List.length_append,
      List.length_cons, ih]; ring

theorem volume_le (rows : List (List Bool)) (L : ℕ)
    (h : ∀ row ∈ rows, row.length ≤ L) : volume rows ≤ rows.length * L := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    have hr := h row (by simp)
    have ht := ih (fun x hx => h x (by simp [hx]))
    simp only [volume_cons, List.length_cons]
    nlinarith

theorem budget_linear (rows : List (List Bool)) (a b : ℕ) :
    RecordPrograms.budget (fun row => a * row.length + b) rows =
      (a + 6) * volume rows + (b + 7) * rows.length := by
  induction rows with
  | nil => simp [RecordPrograms.budget]
  | cons row rows ih =>
    simp only [RecordPrograms.budget, volume_cons, List.length_cons, ih]
    ring

theorem volume_cartesian (rows alphabet : List (List Bool)) :
    volume (TupleProgram.cartesianOutput rows alphabet) =
      alphabet.length * volume rows + rows.length * volume alphabet := by
  unfold TupleProgram.cartesianOutput
  rw [volume_reverse]
  induction rows with
  | nil => simp
  | cons row rows ih =>
    simp only [List.flatMap_cons, volume_append, volume_prefix,
      volume_cons, List.length_cons, ih]
    ring

theorem cartesian_width (rows alphabet : List (List Bool)) (L W : ℕ)
    (hr : ∀ row ∈ rows, row.length ≤ L)
    (ha : ∀ row ∈ alphabet, row.length ≤ W) :
    ∀ row ∈ TupleProgram.cartesianOutput rows alphabet, row.length ≤ L + W := by
  intro row hrow
  simp only [TupleProgram.cartesianOutput, List.mem_reverse, List.mem_flatMap,
    List.mem_map] at hrow
  obtain ⟨pref, hp, word, hw, rfl⟩ := hrow
  simpa only [List.length_append] using Nat.add_le_add (hr pref hp) (ha word hw)

theorem tupleCost_eq (alphabet : List (List Bool)) (row : List Bool) :
    TupleProgram.tupleCost alphabet row =
      (12 * alphabet.length + 2) * row.length +
        25 * volume alphabet + 36 * alphabet.length + 18 := by
  have hb : RecordPrograms.budget (fun x => 5 * x.length + 12 * row.length + 15) alphabet =
      (5 + 6) * volume alphabet + (12 * row.length + 15 + 7) * alphabet.length := by
    simpa only [Nat.add_assoc] using budget_linear alphabet 5 (12 * row.length + 15)
  rw [TupleProgram.tupleCost, ProgramEncoding.encodeRecords_length, hb]
  dsimp only [volume]
  ring

theorem expansionCost_eq (rows alphabet : List (List Bool)) :
    TupleProgram.expansionCost rows alphabet =
      3 + (12 * alphabet.length + 8) * volume rows +
        (25 * volume alphabet + 36 * alphabet.length + 25) * rows.length := by
  unfold TupleProgram.expansionCost
  have hf : TupleProgram.tupleCost alphabet = fun row =>
      (12 * alphabet.length + 2) * row.length +
        (25 * volume alphabet + 36 * alphabet.length + 18) := by
    funext row
    simpa only [Nat.add_assoc] using tupleCost_eq alphabet row
  rw [hf, budget_linear]
  ring

theorem stepCost_eq (rows alphabet : List (List Bool)) :
    TupleProgram.stepCost rows alphabet =
      17 + (24 * alphabet.length + 8) * volume rows +
        (37 * volume alphabet + 48 * alphabet.length + 25) * rows.length := by
  rw [TupleProgram.stepCost, expansionCost_eq, ProgramEncoding.encodeRecords_length]
  change 3 + (12 * alphabet.length + 8) * volume rows +
      (25 * volume alphabet + 36 * alphabet.length + 25) * rows.length +
      6 * (2 * volume (TupleProgram.cartesianOutput rows alphabet) +
        2 * (TupleProgram.cartesianOutput rows alphabet).length + 1) + 8 = _
  rw [volume_cartesian, TupleProgram.cartesianOutput_length]
  ring

/-- One actual expansion, including its loop overhead, has a uniform bound
in the number and maximum width of its input records. -/
theorem stepCost_add_two_le (rows alphabet : List (List Bool)) (L W : ℕ)
    (hr : ∀ row ∈ rows, row.length ≤ L)
    (ha : ∀ row ∈ alphabet, row.length ≤ W) :
    TupleProgram.stepCost rows alphabet + 2 ≤
      200 * (rows.length + 1) * (alphabet.length + 1) * (L + W + 1) := by
  have hv := volume_le rows L hr
  have hu := volume_le alphabet W ha
  rw [stepCost_eq]
  calc
    _ = 19 + (24 * alphabet.length + 8) * volume rows +
        (37 * volume alphabet + 48 * alphabet.length + 25) * rows.length := by ring
    _ ≤ 19 + (24 * alphabet.length + 8) * (rows.length * L) +
        (37 * (alphabet.length * W) + 48 * alphabet.length + 25) * rows.length := by
      gcongr
    _ ≤ _ + (176 * rows.length * alphabet.length * L + 163 * rows.length * alphabet.length * W +
        152 * rows.length * alphabet.length + 192 * rows.length * L + 200 * rows.length * W +
        175 * rows.length + 200 * alphabet.length * L + 200 * alphabet.length * W +
        200 * alphabet.length + 200 * L + 200 * W + 181) := Nat.le_add_right _ _
    _ = _ := by ring

/-- The actual repeated Cartesian expansion is linear in its final tuple
count, with a fixed polynomial factor in depth and physical word width. -/
theorem powerCost_le (alphabet rows : List (List Bool)) (n L W : ℕ)
    (hA : 1 ≤ alphabet.length)
    (hr : ∀ row ∈ rows, row.length ≤ L)
    (ha : ∀ row ∈ alphabet, row.length ≤ W) :
    TupleProgram.powerCost alphabet n rows ≤
      400 * (n + 1) * (rows.length + 1) * alphabet.length ^ n * (L + n * W + W + 1) := by
  induction n generalizing rows L with
  | zero =>
    simp only [TupleProgram.powerCost, Nat.zero_add, pow_zero, Nat.mul_one, Nat.zero_mul]
    nlinarith
  | succ n ih =>
    have hi := ih (TupleProgram.cartesianOutput rows alphabet) (L + W)
      (cartesian_width rows alphabet L W hr ha)
    rw [TupleProgram.cartesianOutput_length] at hi
    have hs := stepCost_add_two_le rows alphabet L W hr ha
    have hA' : alphabet.length + 1 ≤ 2 * alphabet.length := by omega
    have hs' : TupleProgram.stepCost rows alphabet + 2 ≤
        400 * (rows.length + 1) * alphabet.length * (L + W + 1) := by
      calc
        _ ≤ 200 * (rows.length + 1) * (alphabet.length + 1) * (L + W + 1) := hs
        _ ≤ 200 * (rows.length + 1) * (2 * alphabet.length) * (L + W + 1) := by gcongr
        _ = _ := by ring
    have hpow : alphabet.length ≤ alphabet.length ^ (n + 1) := by
      simpa only [pow_one] using pow_le_pow_right₀ hA (show 1 ≤ n + 1 by omega)
    have hwidth : L + W + 1 ≤ L + (n + 1) * W + W + 1 := by nlinarith
    have hstep : TupleProgram.stepCost rows alphabet + 2 ≤
        400 * (rows.length + 1) * alphabet.length ^ (n + 1) *
          (L + (n + 1) * W + W + 1) := by
      exact hs'.trans (by gcongr)
    have hrA : rows.length * alphabet.length + 1 ≤ (rows.length + 1) * alphabet.length := by
      nlinarith
    have hrec : TupleProgram.powerCost alphabet n (TupleProgram.cartesianOutput rows alphabet) ≤
        400 * (n + 1) * (rows.length + 1) * alphabet.length ^ (n + 1) *
          (L + (n + 1) * W + W + 1) := by
      calc
        _ ≤ 400 * (n + 1) * (rows.length * alphabet.length + 1) * alphabet.length ^ n *
            (L + W + n * W + W + 1) := hi
        _ ≤ 400 * (n + 1) * ((rows.length + 1) * alphabet.length) * alphabet.length ^ n *
            (L + W + n * W + W + 1) := by gcongr
        _ = _ := by rw [pow_succ]; ring
    rw [TupleProgram.powerCost]
    have hsum := Nat.add_le_add hstep hrec
    nlinarith

theorem generated_powerCost_le (alphabet : List (List Bool)) (n W : ℕ)
    (hA : 1 ≤ alphabet.length) (ha : ∀ row ∈ alphabet, row.length ≤ W) :
    TupleProgram.powerCost alphabet n [[]] ≤
      800 * (n + 1) * alphabet.length ^ n * ((n + 1) * W + 1) := by
  have h := powerCost_le alphabet [[]] n 0 W hA (by simp) ha
  calc
    _ ≤ 400 * (n + 1) * ([[]] : List (List Bool)).length.succ * alphabet.length ^ n *
        (0 + n * W + W + 1) := h
    _ = _ := by simp only [List.length_cons, List.length_nil, Nat.succ_eq_add_one]; ring

end SubexponentialSAT.Subexp.PairScoreBounds

end OAI.Algorithms
