import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BinaryArithmetic
import OAI.Algorithms.SubexponentialSAT.Computation
import OAI.Algorithms.SubexponentialSAT.NilpotentDefect

namespace OAI.Algorithms

/-!
# Binary long division with finite-bit operations

The executable functions below inspect Bool/list constructors only: they do not
call Nat division, multiplication, comparison, or subtraction on encoded values.
Natural arithmetic appears solely in specifications and event-count proofs.
The event count is not asserted to be a primitive Turing-machine runtime.
-/

namespace SubexponentialSAT.ModularArithmetic

open SubexponentialSAT.BinaryArithmetic

theorem bitVal_le_one (b : Bool) : bitVal b ≤ 1 := by
  cases b <;> decide

theorem toNat_lt_pow_length (xs : List Bool) : BinaryArithmetic.toNat xs < 2 ^ xs.length := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
    have hb := bitVal_le_one b
    simp only [toNat_cons, List.length_cons, pow_succ]
    omega

/-- One complete binary subtraction cell. -/
def differenceBit (a b borrow : Bool) : Bool := (a ^^ b) ^^ borrow

def borrowBit (a b borrow : Bool) : Bool :=
  ((!a) && (b || borrow)) || (b && borrow)

theorem fullSubtractor_correct (a b borrow : Bool) :
    bitVal a + 2 * bitVal (borrowBit a b borrow) =
      bitVal b + bitVal borrow + bitVal (differenceBit a b borrow) := by
  cases a <;> cases b <;> cases borrow <;> decide

/-- Fixed-width subtraction. Its specifications require equal input widths.
The unmatched cases only make the executable function total. -/
def subCarry : Bool → List Bool → List Bool → List Bool × Bool
  | c, [], _ => ([], c)
  | c, _ :: _, [] => ([], c)
  | c, a :: as, b :: bs =>
    let tail := subCarry (borrowBit a b c) as bs
    (differenceBit a b c :: tail.1, tail.2)

theorem subCarry_length (c : Bool) (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    (subCarry c xs ys).1.length = xs.length := by
  induction xs generalizing ys c with
  | nil => simp [subCarry]
  | cons a as ih =>
    cases ys with
    | nil => simp at hlen
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simpa [subCarry] using congrArg Nat.succ (ih (borrowBit a b c) bs hlen)

theorem subCarry_correct (c : Bool) (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    BinaryArithmetic.toNat xs + 2 ^ xs.length * bitVal (subCarry c xs ys).2 =
      BinaryArithmetic.toNat ys + bitVal c + BinaryArithmetic.toNat (subCarry c xs ys).1 := by
  induction xs generalizing ys c with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp hlen.symm
    subst ys
    simp [subCarry]
  | cons a as ih =>
    cases ys with
    | nil => simp at hlen
    | cons b bs =>
      have hl : as.length = bs.length := by simpa using hlen
      have ht := ih (borrowBit a b c) bs hl
      have hb := fullSubtractor_correct a b c
      simp only [subCarry, toNat_cons, List.length_cons, pow_succ]
      nlinarith

theorem subCarry_borrow_iff (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    (subCarry false xs ys).2 = true ↔ BinaryArithmetic.toNat xs < BinaryArithmetic.toNat ys := by
  have hv := subCarry_correct false xs ys hlen
  have hd := toNat_lt_pow_length (subCarry false xs ys).1
  rw [subCarry_length false xs ys hlen] at hd
  cases hc : (subCarry false xs ys).2 <;> simp [hc, bitVal] at hv ⊢ <;> omega

/-- Copy the given bits into a word with the requested shape, adding zero
bits at the most significant end. No lengths are calculated by the routine. -/
def padTo : List Bool → List Bool → List Bool
  | [], _ => []
  | _ :: shape, [] => false :: padTo shape []
  | _ :: shape, b :: bs => b :: padTo shape bs

theorem padTo_length (shape xs : List Bool) :
    (padTo shape xs).length = shape.length := by
  induction shape generalizing xs with
  | nil => rfl
  | cons b shape ih =>
    cases xs <;> simp [padTo, ih]

theorem padTo_correct (shape xs : List Bool) (hlen : xs.length ≤ shape.length) :
    BinaryArithmetic.toNat (padTo shape xs) = BinaryArithmetic.toNat xs := by
  induction shape generalizing xs with
  | nil =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst xs
    rfl
  | cons b shape ih =>
    cases xs with
    | nil => simp [padTo, ih [] (Nat.zero_le _), bitVal]
    | cons a as =>
      have hl : as.length ≤ shape.length := by simpa using hlen
      simp [padTo, toNat_cons, ih as hl]

/-- Shift the current remainder, then use one fixed-width subtraction and
its final borrow bit to select the new remainder. -/
def shiftReduce (modulus remainder : List Bool) (b : Bool) : List Bool :=
  let shifted := b :: remainder
  let difference := subCarry false shifted (padTo shifted modulus)
  if difference.2 then shifted else difference.1

theorem shiftReduce_length (m r : List Bool) (b : Bool) :
    (shiftReduce m r b).length = r.length + 1 := by
  dsimp only [shiftReduce]
  split
  · rfl
  · simpa using subCarry_length false (b :: r) (padTo (b :: r) m)
      (padTo_length (b :: r) m).symm

theorem shiftReduce_correct (m r : List Bool) (b : Bool)
    (hlen : m.length ≤ r.length) (_hm : 0 < BinaryArithmetic.toNat m)
    (hr : BinaryArithmetic.toNat r < BinaryArithmetic.toNat m) :
    BinaryArithmetic.toNat (shiftReduce m r b) = (bitVal b + 2 * BinaryArithmetic.toNat r) % BinaryArithmetic.toNat m := by
  let shifted := b :: r
  let padded := padTo shifted m
  have hlength : shifted.length = padded.length := (padTo_length shifted m).symm
  have hpadded : BinaryArithmetic.toNat padded = BinaryArithmetic.toNat m :=
    padTo_correct shifted m (by simpa [shifted] using Nat.le_trans hlen (Nat.le_succ _))
  have hv := subCarry_correct false shifted padded hlength
  have hc := subCarry_borrow_iff shifted padded hlength
  have hb := bitVal_le_one b
  have hsmall : BinaryArithmetic.toNat shifted < 2 * BinaryArithmetic.toNat m := by
    simp only [shifted, toNat_cons]
    omega
  change BinaryArithmetic.toNat (if (subCarry false shifted padded).2 then shifted
    else (subCarry false shifted padded).1) = BinaryArithmetic.toNat shifted % BinaryArithmetic.toNat m
  cases hborrow : (subCarry false shifted padded).2 with
  | false =>
    have hid : BinaryArithmetic.toNat shifted = BinaryArithmetic.toNat m + BinaryArithmetic.toNat (subCarry false shifted padded).1 := by
      simpa only [hborrow, bitVal, Bool.false_eq_true, ↓reduceIte,
        mul_zero, add_zero, hpadded] using hv
    have hd : BinaryArithmetic.toNat (subCarry false shifted padded).1 < BinaryArithmetic.toNat m := by omega
    simp only [ Bool.false_eq_true, ↓reduceIte]
    rw [hid, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hd]
  | true =>
    have hlt : BinaryArithmetic.toNat shifted < BinaryArithmetic.toNat m := by
      simpa only [hpadded] using hc.mp hborrow
    simp only [ ↓reduceIte, Nat.mod_eq_of_lt hlt]

/-- Long division processes the most significant input bit first by recursion
on the tail of a little-endian word. The remainder width grows harmlessly. -/
def reduce (modulus : List Bool) : List Bool → List Bool
  | [] => padTo modulus []
  | b :: bs => shiftReduce modulus (reduce modulus bs) b

theorem reduce_length (m xs : List Bool) :
    (reduce m xs).length = m.length + xs.length := by
  induction xs with
  | nil => simp [reduce, padTo_length]
  | cons b bs ih => simp [reduce, shiftReduce_length, ih, Nat.add_assoc]

/-- Correct modular reduction, proved without Nat division in the algorithm. -/
theorem reduce_correct (m xs : List Bool) (hm : 0 < BinaryArithmetic.toNat m) :
    BinaryArithmetic.toNat (reduce m xs) = BinaryArithmetic.toNat xs % BinaryArithmetic.toNat m := by
  induction xs with
  | nil =>
    simpa [reduce] using padTo_correct m [] (Nat.zero_le _)
  | cons b bs ih =>
    rw [reduce, shiftReduce_correct]
    · simp only [toNat_cons, ih, Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
    · rw [reduce_length]
      omega
    · exact hm
    · rw [ih]
      exact Nat.mod_lt _ hm

/-! A measured finite-control subtraction transducer. -/

structure SubState where
  left : List Bool
  right : List Bool
  output : List Bool
  borrow : Bool

/-- One transition reads two bits, changes one Boolean register, and pushes
one bit. It never evaluates the natural number represented by a stack. -/
def subStep : SubState → Option SubState
  | ⟨a :: as, b :: bs, output, c⟩ =>
      some ⟨as, bs, differenceBit a b c :: output, borrowBit a b c⟩
  | _ => none

theorem subCarry_trace (c : Bool) (xs ys output : List Bool)
    (hlen : xs.length = ys.length) :
    SubexponentialSAT.Computation.Trace subStep xs.length
      ⟨xs, ys, output, c⟩
      ⟨[], [], (subCarry c xs ys).1.reverse ++ output, (subCarry c xs ys).2⟩ := by
  induction xs generalizing ys output c with
  | nil =>
    have hy : ys = [] := List.length_eq_zero_iff.mp hlen.symm
    subst ys
    simpa [subCarry] using SubexponentialSAT.Computation.Trace.refl
      (step := subStep) (⟨[], [], output, c⟩ : SubState)
  | cons a as ih =>
    cases ys with
    | nil => simp at hlen
    | cons b bs =>
      have hl : as.length = bs.length := by simpa using hlen
      refine SubexponentialSAT.Computation.Trace.cons (b :=
        ⟨as, bs, differenceBit a b c :: output, borrowBit a b c⟩) rfl ?_
      simpa [subCarry, List.reverse_cons, List.append_assoc] using
        ih (borrowBit a b c) bs (differenceBit a b c :: output) hl

theorem subCarry_terminal (c : Bool) (xs ys output : List Bool) :
    subStep ⟨[], [], (subCarry c xs ys).1.reverse ++ output,
      (subCarry c xs ys).2⟩ = none := rfl

structure PadState where
  shape : List Bool
  input : List Bool
  output : List Bool

def padStep : PadState → Option PadState
  | ⟨_ :: shape, [], output⟩ => some ⟨shape, [], false :: output⟩
  | ⟨_ :: shape, b :: bs, output⟩ => some ⟨shape, bs, b :: output⟩
  | _ => none

theorem padTo_trace (shape xs output : List Bool)
    (hlen : xs.length ≤ shape.length) :
    SubexponentialSAT.Computation.Trace padStep shape.length
      ⟨shape, xs, output⟩
      ⟨[], [], (padTo shape xs).reverse ++ output⟩ := by
  induction shape generalizing xs output with
  | nil =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst xs
    simpa [padTo] using SubexponentialSAT.Computation.Trace.refl
      (step := padStep) (⟨[], [], output⟩ : PadState)
  | cons b shape ih =>
    cases xs with
    | nil =>
      refine SubexponentialSAT.Computation.Trace.cons (b := ⟨shape, [], false :: output⟩) rfl ?_
      simpa [padTo, List.reverse_cons, List.append_assoc] using
        ih [] (false :: output) (Nat.zero_le _)
    | cons a as =>
      have hl : as.length ≤ shape.length := by simpa using hlen
      refine SubexponentialSAT.Computation.Trace.cons (b := ⟨shape, as, a :: output⟩) rfl ?_
      simpa [padTo, List.reverse_cons, List.append_assoc] using
        ih as (a :: output) hl

/-! Instrumentation with events carrying only finitely many Boolean values.
The logs record every padding/subtraction cell and each shift/selection.
They are not a primitive-machine simulation certificate. -/

inductive Event where
  | pad (bit : Bool)
  | subtract (left right borrow : Bool)
  | shift (bit : Bool)
  | select (borrow : Bool)
  deriving DecidableEq

def padEvents : List Bool → List Bool → List Event
  | [], _ => []
  | _ :: shape, [] => Event.pad false :: padEvents shape []
  | _ :: shape, b :: bs => Event.pad b :: padEvents shape bs

theorem padEvents_length (shape xs : List Bool) :
    (padEvents shape xs).length = shape.length := by
  induction shape generalizing xs with
  | nil => rfl
  | cons b shape ih => cases xs <;> simp [padEvents, ih]

def subEvents : Bool → List Bool → List Bool → List Event
  | _, [], _ => []
  | _, _ :: _, [] => []
  | c, a :: as, b :: bs =>
    Event.subtract a b c :: subEvents (borrowBit a b c) as bs

theorem subEvents_length (c : Bool) (xs ys : List Bool)
    (hlen : xs.length = ys.length) :
    (subEvents c xs ys).length = xs.length := by
  induction xs generalizing ys c with
  | nil => rfl
  | cons a as ih =>
    cases ys with
    | nil => simp at hlen
    | cons b bs =>
      have hl : as.length = bs.length := by simpa using hlen
      simp [subEvents, ih (borrowBit a b c) bs hl]

/-- The subtraction portion of the logged execution is an actual measured
trace, of exactly the event count, of the finite-control transducer. -/
theorem subEvents_trace (c : Bool) (xs ys output : List Bool)
    (hlen : xs.length = ys.length) :
    SubexponentialSAT.Computation.Trace subStep (subEvents c xs ys).length
      ⟨xs, ys, output, c⟩
      ⟨[], [], (subCarry c xs ys).1.reverse ++ output, (subCarry c xs ys).2⟩ := by
  rw [subEvents_length c xs ys hlen]
  exact subCarry_trace c xs ys output hlen

def shiftLogged (m r : List Bool) (b : Bool) : List Bool × List Event :=
  let shifted := b :: r
  let padded := padTo shifted m
  let difference := subCarry false shifted padded
  (if difference.2 then shifted else difference.1,
    [Event.shift b] ++ padEvents shifted m ++ subEvents false shifted padded ++
      [Event.select difference.2])

theorem shiftLogged_value (m r : List Bool) (b : Bool) :
    (shiftLogged m r b).1 = shiftReduce m r b := rfl

theorem shiftLogged_count (m r : List Bool) (b : Bool) :
    (shiftLogged m r b).2.length = 2 * r.length + 4 := by
  simp only [shiftLogged, List.length_append, padEvents_length,
    subEvents_length false (b :: r) (padTo (b :: r) m)
      (padTo_length (b :: r) m).symm, List.length_cons, List.length_nil]
  omega

/-- A complete binary-reduction execution with its finite-operation log. -/
def reduceLogged (m : List Bool) : List Bool → List Bool × List Event
  | [] => (padTo m [], padEvents m [])
  | b :: bs =>
    let tail := reduceLogged m bs
    let head := shiftLogged m tail.1 b
    (head.1, tail.2 ++ head.2)

theorem reduceLogged_value (m xs : List Bool) :
    (reduceLogged m xs).1 = reduce m xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [reduceLogged, shiftLogged_value, ih, reduce]

theorem reduceLogged_correct (m xs : List Bool) (hm : 0 < BinaryArithmetic.toNat m) :
    BinaryArithmetic.toNat (reduceLogged m xs).1 = BinaryArithmetic.toNat xs % BinaryArithmetic.toNat m := by
  rw [reduceLogged_value]
  exact reduce_correct m xs hm

/-- Exact count: m padding cells, then two scans and two finite operations
for each input bit. Remainder width grows by one bit at each stage. -/
theorem reduceLogged_count (m xs : List Bool) :
    (reduceLogged m xs).2.length =
      m.length + 2 * m.length * xs.length + xs.length * xs.length + 3 * xs.length := by
  induction xs with
  | nil => simp [reduceLogged, padEvents_length]
  | cons b bs ih =>
    simp only [reduceLogged, List.length_append, shiftLogged_count,
      reduceLogged_value, reduce_length, ih, List.length_cons]
    ring

/-- A quadratic bound in a common input-word width. This counts concrete
finite-operation events, not assumed unit-time arithmetic on Naturals. -/
theorem reduceLogged_count_le (m xs : List Bool) (B : ℕ)
    (hm : m.length ≤ B) (hx : xs.length ≤ B) :
    (reduceLogged m xs).2.length ≤ 3 * B * B + 4 * B := by
  rw [reduceLogged_count]
  have hmx := Nat.mul_le_mul hm hx
  have hxx := Nat.mul_le_mul hx hx
  nlinarith

theorem reduce_prime_power_correct (m xs : List Bool) (p D : ℕ)
    (hp : 0 < p) (hm : BinaryArithmetic.toNat m = p ^ (D + 1)) :
    BinaryArithmetic.toNat (reduceLogged m xs).1 = BinaryArithmetic.toNat xs % p ^ (D + 1) := by
  rw [reduceLogged_correct m xs (by rw [hm]; exact pow_pos hp _), hm]

/-! Modular addition and multiplication combine the concrete binary
arithmetic runs with the concrete long-division run. -/

abbrev ModularEvent := SubexponentialSAT.BinaryArithmetic.BitEvent ⊕ Event

def addModRun (m xs ys : List Bool) : List Bool × List ModularEvent :=
  let added := SubexponentialSAT.BinaryArithmetic.addRun false xs ys
  let reduced := reduceLogged m added.1
  (reduced.1, added.2.map Sum.inl ++ reduced.2.map Sum.inr)

def mulModRun (m xs ys : List Bool) : List Bool × List ModularEvent :=
  let product := SubexponentialSAT.BinaryArithmetic.mulRun xs ys
  let reduced := reduceLogged m product.1
  (reduced.1, product.2.map Sum.inl ++ reduced.2.map Sum.inr)

theorem addModRun_correct (m xs ys : List Bool) (hm : 0 < BinaryArithmetic.toNat m) :
    BinaryArithmetic.toNat (addModRun m xs ys).1 = (BinaryArithmetic.toNat xs + BinaryArithmetic.toNat ys) % BinaryArithmetic.toNat m := by
  simp only [addModRun, reduceLogged_correct _ _ hm]
  rw [(SubexponentialSAT.BinaryArithmetic.addRun_correct_and_cost false xs ys).1]
  simp

theorem mulModRun_correct (m xs ys : List Bool) (hm : 0 < BinaryArithmetic.toNat m) :
    BinaryArithmetic.toNat (mulModRun m xs ys).1 = (BinaryArithmetic.toNat xs * BinaryArithmetic.toNat ys) % BinaryArithmetic.toNat m := by
  simp only [mulModRun, reduceLogged_correct _ _ hm]
  rw [(SubexponentialSAT.BinaryArithmetic.mulRun_correct_and_cost xs ys).1]

theorem addModRun_count (m xs ys : List Bool) (B : ℕ)
    (hm : m.length ≤ B) (hx : xs.length ≤ B) (hy : ys.length ≤ B) :
    (addModRun m xs ys).2.length ≤ 20 * (B + 1) ^ 2 := by
  have ha := (SubexponentialSAT.BinaryArithmetic.addRun_correct_and_cost false xs ys).2
  have hmax : max xs.length ys.length ≤ B := max_le hx hy
  have hwidth : (SubexponentialSAT.BinaryArithmetic.addRun false xs ys).1.length ≤ B + 1 := by
    rw [SubexponentialSAT.BinaryArithmetic.addRun_eq]
    exact (SubexponentialSAT.BinaryArithmetic.length_addCarry false xs ys).trans (Nat.add_le_add_right hmax 1)
  have hr := reduceLogged_count_le m (SubexponentialSAT.BinaryArithmetic.addRun false xs ys).1
    (B + 1) (by omega) hwidth
  simp only [addModRun, List.length_append, List.length_map]
  nlinarith

theorem mulModRun_count (m xs ys : List Bool) (B : ℕ)
    (hm : m.length ≤ B) (hx : xs.length ≤ B) (hy : ys.length ≤ B) :
    (mulModRun m xs ys).2.length ≤ 200 * (B + 1) ^ 2 := by
  have hp := (SubexponentialSAT.BinaryArithmetic.mulRun_correct_and_cost xs ys).2
  have hwidth : (SubexponentialSAT.BinaryArithmetic.mulRun xs ys).1.length ≤ 3 * B := by
    rw [SubexponentialSAT.BinaryArithmetic.mulRun_eq]
    have hw := SubexponentialSAT.BinaryArithmetic.length_mul xs ys
    dsimp only
    omega
  have hr := reduceLogged_count_le m (SubexponentialSAT.BinaryArithmetic.mulRun xs ys).1
    (3 * B) (by omega) hwidth
  have hproduct : (xs.length + 1) * (xs.length + ys.length + 1) ≤
      (B + 1) * (2 * B + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  simp only [mulModRun, List.length_append, List.length_map]
  nlinarith

/-! An explicit finite ring expression for geometric correction. Its
operation-node count is a ring-operation bound, separately from bit costs. -/

inductive RingExpr where
  | inputA
  | inputB
  | zero
  | one
  | add (left right : RingExpr)
  | sub (left right : RingExpr)
  | mul (left right : RingExpr)

def RingExpr.eval {R : Type*} [CommRing R] (a b : R) : RingExpr → R
  | .inputA => a
  | .inputB => b
  | .zero => 0
  | .one => 1
  | .add left right => left.eval a b + right.eval a b
  | .sub left right => left.eval a b - right.eval a b
  | .mul left right => left.eval a b * right.eval a b

def RingExpr.operations : RingExpr → ℕ
  | .inputA | .inputB | .zero | .one => 0
  | .add left right | .sub left right | .mul left right =>
      left.operations + right.operations + 1

def RingExpr.multiplications : RingExpr → ℕ
  | .inputA | .inputB | .zero | .one => 0
  | .add left right | .sub left right => left.multiplications + right.multiplications
  | .mul left right => left.multiplications + right.multiplications + 1

def errorExpr : RingExpr := .sub .one (.mul .inputA .inputB)

/-- Horner evaluation avoids separately constructing all the powers. -/
def geometricExpr : ℕ → RingExpr
  | 0 => .zero
  | n + 1 => .add (.mul errorExpr (geometricExpr n)) .one

def inverseExpr (μ : ℕ) : RingExpr := .mul .inputB (geometricExpr μ)

theorem geometricExpr_eval {R : Type*} [CommRing R] (a b : R) (μ : ℕ) :
    (geometricExpr μ).eval a b =
      ∑ j ∈ Finset.range μ, (1 - a * b) ^ j := by
  induction μ with
  | zero => simp [geometricExpr, RingExpr.eval]
  | succ μ ih =>
    simp only [geometricExpr, RingExpr.eval, errorExpr, ih, geom_sum_succ]

theorem inverseExpr_eval {R : Type*} [CommRing R] (a b : R) (μ : ℕ) :
    (inverseExpr μ).eval a b = SubexponentialSAT.NilpotentDefect.geometricInverse a b μ := by
  simp [inverseExpr, RingExpr.eval, geometricExpr_eval,
    SubexponentialSAT.NilpotentDefect.geometricInverse]

theorem inverseExpr_correct {R : Type*} [CommRing R] (a b : R) (μ : ℕ)
    (hnil : (1 - a * b) ^ μ = 0) :
    a * (inverseExpr μ).eval a b = 1 := by
  rw [inverseExpr_eval]
  exact SubexponentialSAT.NilpotentDefect.mul_geometricInverse a b μ hnil

theorem geometricExpr_operations (μ : ℕ) :
    (geometricExpr μ).operations = 4 * μ := by
  induction μ with
  | zero => rfl
  | succ μ ih => simp [geometricExpr, RingExpr.operations, errorExpr, ih]; omega

theorem geometricExpr_multiplications (μ : ℕ) :
    (geometricExpr μ).multiplications = 2 * μ := by
  induction μ with
  | zero => rfl
  | succ μ ih => simp [geometricExpr, RingExpr.multiplications, errorExpr, ih]; omega

/-- The explicit inverse expression uses exactly 4μ+1 ring operations. -/
theorem inverseExpr_operations (μ : ℕ) :
    (inverseExpr μ).operations = 4 * μ + 1 := by
  simp [inverseExpr, RingExpr.operations, geometricExpr_operations]

/-- Of those operations, exactly 2μ+1 are multiplications. -/
theorem inverseExpr_multiplications (μ : ℕ) :
    (inverseExpr μ).multiplications = 2 * μ + 1 := by
  simp [inverseExpr, RingExpr.multiplications, geometricExpr_multiplications]

end SubexponentialSAT.ModularArithmetic

end OAI.Algorithms
