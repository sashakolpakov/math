import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

namespace OAI.Algorithms

/-!
# Binary modular negation for fixed-width base coefficients

The data path creates a width-(B+1) zero shape, pads both operands, performs
the verified bitwise subtraction, reduces the difference, and normalizes to
B bits. Reduction is uniform, including x=0 and modulus=2^B. Encoded values
are never decoded by the algorithm. The event list records actual finite
bit/constructor operations; its length is not claimed to be a Turing runtime.
-/

namespace SubexponentialSAT.SubexpBaseNegation

open SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.ModularArithmetic
open SubexponentialSAT.SubexpLiftRing

/-- Build a zero shape and record each emitted bit. -/
def zerosLogged : ℕ → List Bool × List Event
  | 0 => ([], [])
  | n + 1 =>
      let out := zerosLogged n
      (false :: out.1, Event.pad false :: out.2)

@[simp] theorem zerosLogged_value (n : ℕ) :
    (zerosLogged n).1 = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [zerosLogged, ih, List.replicate_succ]

@[simp] theorem zerosLogged_count (n : ℕ) : (zerosLogged n).2.length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [zerosLogged, ih]

/-- Copy a bounded prefix, recording every copied bit. -/
def takeLogged : ℕ → List Bool → List Bool × List Event
  | 0, _ => ([], [])
  | _ + 1, [] => ([], [])
  | n + 1, b :: bs =>
      let out := takeLogged n bs
      (b :: out.1, Event.pad b :: out.2)

@[simp] theorem takeLogged_value (n : ℕ) (xs : List Bool) :
    (takeLogged n xs).1 = xs.take n := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih => cases xs <;> simp [takeLogged, ih]

theorem takeLogged_count (n : ℕ) (xs : List Bool) :
    (takeLogged n xs).2.length = min n xs.length := by
  induction n generalizing xs with
  | zero => simp [takeLogged]
  | succ n ih => cases xs <;> simp [takeLogged, ih, Nat.succ_min_succ]

/-- The same value as normalizeBits, with explicit shape/copy/padding events. -/
def normalizeLogged (B : ℕ) (xs : List Bool) : List Bool × List Event :=
  let shape := zerosLogged B
  let front := takeLogged B xs
  (padTo shape.1 front.1,
    shape.2 ++ front.2 ++ padEvents shape.1 front.1)

@[simp] theorem normalizeLogged_value (B : ℕ) (xs : List Bool) :
    (normalizeLogged B xs).1 = normalizeBits B xs := by
  simp [normalizeLogged, normalizeBits]

theorem normalizeLogged_count (B : ℕ) (xs : List Bool) :
    (normalizeLogged B xs).2.length = 2 * B + min B xs.length := by
  simp only [normalizeLogged, List.length_append, zerosLogged_count, takeLogged_count,
    padEvents_length, zerosLogged_value, List.length_replicate]
  omega

theorem normalizeLogged_count_le (B : ℕ) (xs : List Bool) :
    (normalizeLogged B xs).2.length ≤ 3 * B := by
  rw [normalizeLogged_count]
  have := Nat.min_le_left B xs.length
  omega

def padded (B : ℕ) (xs : List Bool) : List Bool :=
  padTo (List.replicate (B + 1) false) xs

@[simp] theorem padded_length (B : ℕ) (xs : List Bool) :
    (padded B xs).length = B + 1 := by simp [padded, padTo_length]

theorem padded_value (B : ℕ) (xs : List Bool) (hx : xs.length ≤ B + 1) :
    BinaryArithmetic.toNat (padded B xs) = BinaryArithmetic.toNat xs :=
  padTo_correct _ xs (by simpa using hx)

def difference (B : ℕ) (m xs : List Bool) : List Bool × Bool :=
  subCarry false (padded B m) (padded B xs)

@[simp] theorem difference_length (B : ℕ) (m xs : List Bool) :
    (difference B m xs).1.length = B + 1 := by
  rw [difference, subCarry_length false _ _ (by simp), padded_length]

theorem difference_value (B : ℕ) (m xs : List Bool)
    (hm : m.length ≤ B + 1) (hx : xs.length ≤ B)
    (hvalue : BinaryArithmetic.toNat xs ≤ BinaryArithmetic.toNat m) :
    BinaryArithmetic.toNat (difference B m xs).1 = BinaryArithmetic.toNat m - BinaryArithmetic.toNat xs := by
  have hlen : (padded B m).length = (padded B xs).length := by simp
  have hpadm := padded_value B m hm
  have hpadx := padded_value B xs (hx.trans (Nat.le_succ B))
  have hborrow : (difference B m xs).2 = false := by
    cases hb : (difference B m xs).2 with
    | false => rfl
    | true =>
        have hlt := (subCarry_borrow_iff (padded B m) (padded B xs) hlen).mp hb
        rw [hpadm, hpadx] at hlt
        omega
  have h := subCarry_correct false (padded B m) (padded B xs) hlen
  change BinaryArithmetic.toNat (padded B m) + 2 ^ (padded B m).length * bitVal (difference B m xs).2 =
    BinaryArithmetic.toNat (padded B xs) + bitVal false + BinaryArithmetic.toNat (difference B m xs).1 at h
  rw [hborrow, bitVal_false, mul_zero, add_zero, hpadm, hpadx, add_zero] at h
  omega

/-- Fixed-width negation using finite bit operations and uniform reduction. -/
def negBaseLogged (B : ℕ) (m xs : List Bool) : List Bool × List Event :=
  let shape := zerosLogged (B + 1)
  let left := padTo shape.1 m
  let right := padTo shape.1 xs
  let diff := subCarry false left right
  let reduced := reduceLogged m diff.1
  let normalized := normalizeLogged B reduced.1
  (normalized.1,
    shape.2 ++ padEvents shape.1 m ++ padEvents shape.1 xs ++
      subEvents false left right ++ reduced.2 ++ normalized.2)

/-- API parallel to addBaseRun/mulBaseRun; the count is an actual log length. -/
def negBaseRun (B : ℕ) (m xs : List Bool) : List Bool × ℕ :=
  let out := negBaseLogged B m xs
  (out.1, out.2.length)

theorem negBaseLogged_output (B : ℕ) (m xs : List Bool) :
    (negBaseLogged B m xs).1 =
      normalizeBits B (reduceLogged m (difference B m xs).1).1 := by
  simp [negBaseLogged, difference, padded]

@[simp] theorem negBaseLogged_length (B : ℕ) (m xs : List Bool) :
    (negBaseLogged B m xs).1.length = B := by
  rw [negBaseLogged_output]
  exact normalizeBits_length _ _

@[simp] theorem negBaseRun_length (B : ℕ) (m xs : List Bool) :
    (negBaseRun B m xs).1.length = B := negBaseLogged_length B m xs

theorem negBaseLogged_value (B : ℕ) (m xs : List Bool)
    (hm : m.length ≤ B + 1) (hx : xs.length ≤ B)
    (hmpos : 0 < BinaryArithmetic.toNat m) (hcap : BinaryArithmetic.toNat m ≤ 2 ^ B)
    (hvalue : BinaryArithmetic.toNat xs < BinaryArithmetic.toNat m) :
    BinaryArithmetic.toNat (negBaseLogged B m xs).1 = (BinaryArithmetic.toNat m - BinaryArithmetic.toNat xs) % BinaryArithmetic.toNat m := by
  rw [negBaseLogged_output, normalizeBits_value]
  · rw [reduceLogged_correct _ _ hmpos, difference_value B m xs hm hx hvalue.le]
  · rw [reduceLogged_correct _ _ hmpos]
    exact (Nat.mod_lt _ hmpos).trans_le hcap

theorem negBaseRun_value (B : ℕ) (m xs : List Bool)
    (hm : m.length ≤ B + 1) (hx : xs.length ≤ B)
    (hmpos : 0 < BinaryArithmetic.toNat m) (hcap : BinaryArithmetic.toNat m ≤ 2 ^ B)
    (hvalue : BinaryArithmetic.toNat xs < BinaryArithmetic.toNat m) :
    BinaryArithmetic.toNat (negBaseRun B m xs).1 = (BinaryArithmetic.toNat m - BinaryArithmetic.toNat xs) % BinaryArithmetic.toNat m :=
  negBaseLogged_value B m xs hm hx hmpos hcap hvalue

theorem negBaseRun_cast (B : ℕ) (m xs : List Bool)
    (hm : m.length ≤ B + 1) (hx : xs.length ≤ B)
    (hmpos : 0 < BinaryArithmetic.toNat m) (hcap : BinaryArithmetic.toNat m ≤ 2 ^ B)
    (hvalue : BinaryArithmetic.toNat xs < BinaryArithmetic.toNat m) :
    (BinaryArithmetic.toNat (negBaseRun B m xs).1 : ZMod (BinaryArithmetic.toNat m)) = -(BinaryArithmetic.toNat xs : ZMod (BinaryArithmetic.toNat m)) := by
  rw [negBaseRun_value B m xs hm hx hmpos hcap hvalue, ZMod.natCast_mod,
    Nat.cast_sub hvalue.le, ZMod.natCast_self, zero_sub]

/-- Exact finite-event count; it does not depend on the encoded input value. -/
theorem negBaseLogged_count_exact (B : ℕ) (m xs : List Bool) :
    (negBaseLogged B m xs).2.length =
      (B + 1) ^ 2 + 2 * m.length * (B + 1) + m.length + 7 * (B + 1) + 3 * B := by
  have hs : (subEvents false (padded B m) (padded B xs)).length = B + 1 := by
    rw [subEvents_length false _ _ (by simp), padded_length]
  have hr := reduceLogged_count m (difference B m xs).1
  rw [difference_length] at hr
  have hn : (normalizeLogged B (reduceLogged m (difference B m xs).1).1).2.length =
      3 * B := by
    rw [normalizeLogged_count, reduceLogged_value, reduce_length, difference_length,
      Nat.min_eq_left (by omega)]
    omega
  dsimp only [difference, padded] at hs hr hn
  simp only [negBaseLogged, List.length_append, zerosLogged_count, zerosLogged_value,
    padEvents_length, List.length_replicate]
  nlinarith

/-- A uniform polynomial bound on the length of the concrete emitted log. -/
theorem negBaseLogged_count (B : ℕ) (m xs : List Bool) (hm : m.length ≤ B + 1) :
    (negBaseLogged B m xs).2.length ≤ 10 * (B + 2) ^ 2 := by
  rw [negBaseLogged_count_exact]
  have hmul := Nat.mul_le_mul_right (2 * (B + 1)) hm
  nlinarith

theorem negBaseRun_cost (B : ℕ) (m xs : List Bool) (hm : m.length ≤ B + 1) :
    (negBaseRun B m xs).2 ≤ 10 * (B + 2) ^ 2 :=
  negBaseLogged_count B m xs hm

/-- The subtraction portion has an actual measured finite-control trace. -/
theorem subtraction_trace (B : ℕ) (m xs output : List Bool) :
    SubexponentialSAT.Computation.Trace subStep (B + 1)
      ⟨padded B m, padded B xs, output, false⟩
      ⟨[], [], (difference B m xs).1.reverse ++ output, (difference B m xs).2⟩ := by
  simpa only [padded_length, difference] using
    subCarry_trace false (padded B m) (padded B xs) output (by simp)

theorem example_neg_five_mod_thirteen :
    (negBaseRun 4 (fixedBits 5 13) (fixedBits 4 5)).1 = fixedBits 4 8 := by decide

theorem example_zero_mod_thirteen :
    (negBaseRun 4 (fixedBits 5 13) (fixedBits 4 0)).1 = fixedBits 4 0 := by decide

theorem example_zero_at_capacity :
    (negBaseRun 4 (fixedBits 5 16) (fixedBits 4 0)).1 = fixedBits 4 0 := by decide

theorem example_last_residue :
    (negBaseRun 4 (fixedBits 5 13) (fixedBits 4 12)).1 = fixedBits 4 1 := by decide

end SubexponentialSAT.SubexpBaseNegation

end OAI.Algorithms
