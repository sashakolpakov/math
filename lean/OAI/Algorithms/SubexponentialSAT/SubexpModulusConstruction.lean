import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BinaryArithmetic
import OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

namespace OAI.Algorithms

/-!
# Constructing the prime-power modulus by binary multiplication

The data routine calls the existing binary `mulRun` once per iteration and
starts with the one-bit representation of one. No natural-number exponentiation
or conversion of the encoded value occurs in the data path. A single final
traced pass trims or zero-pads the output. Cost statements count the concrete
finite-alphabet BitEvent traces, not primitive-machine execution steps.
-/

namespace SubexponentialSAT.SubexpModulusConstruction

open BinaryArithmetic

/-- Repeated binary multiplication. The fixed input is always the first
multiplicand, which keeps the raw representation length polynomial. -/
def powerRawRun (pBits : List Bool) : ℕ → List Bool × List BitEvent
  | 0 => ([true], [.control, .push])
  | n + 1 =>
      let prev := powerRawRun pBits n
      let next := mulRun pBits prev.1
      (next.1, .control :: (prev.2 ++ next.2))

theorem powerRawRun_value (pBits : List Bool) (n : ℕ) :
    BinaryArithmetic.toNat (powerRawRun pBits n).1 = BinaryArithmetic.toNat pBits ^ n := by
  induction n with
  | zero => simp [powerRawRun]
  | succ n ih =>
      change BinaryArithmetic.toNat (mulRun pBits (powerRawRun pBits n).1).1 = _
      rw [(mulRun_correct_and_cost _ _).1, ih, pow_succ']

/-- Even before normalization, output length grows only linearly in the
number of repeated multiplications. -/
theorem powerRawRun_length (pBits : List Bool) (n : ℕ) :
    (powerRawRun pBits n).1.length ≤ 1 + 2 * n * pBits.length := by
  induction n with
  | zero => simp [powerRawRun]
  | succ n ih =>
      change (mulRun pBits (powerRawRun pBits n).1).1.length ≤ _
      calc
        _ ≤ 2 * pBits.length + (powerRawRun pBits n).1.length := by
          simpa only [mulRun_eq] using length_mul pBits (powerRawRun pBits n).1
        _ ≤ 2 * pBits.length + (1 + 2 * n * pBits.length) := Nat.add_le_add_left ih _
        _ = 1 + 2 * (n + 1) * pBits.length := by ring

/-- One common budget bounds every multiplication up to the specified limit. -/
theorem powerRawRun_cost_le (pBits : List Bool) (limit n : ℕ) (hn : n ≤ limit) :
    (powerRawRun pBits n).2.length ≤
      2 + n * (1 + 40 * (pBits.length + 1) *
        (pBits.length + 2 + 2 * limit * pBits.length)) := by
  induction n with
  | zero => simp [powerRawRun]
  | succ n ih =>
      have hn' : n ≤ limit := Nat.le_trans (Nat.le_succ n) hn
      have hprev := ih hn'
      have hlen : (powerRawRun pBits n).1.length ≤
          1 + 2 * limit * pBits.length := by
        refine (powerRawRun_length pBits n).trans ?_
        exact Nat.add_le_add_left
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 hn')) 1
      have hmul := (mulRun_correct_and_cost pBits (powerRawRun pBits n).1).2
      have hstep : (mulRun pBits (powerRawRun pBits n).1).2.length ≤
          40 * (pBits.length + 1) * (pBits.length + 2 + 2 * limit * pBits.length) := by
        refine hmul.trans (Nat.mul_le_mul_left _ ?_)
        omega
      change (.control :: ((powerRawRun pBits n).2 ++
        (mulRun pBits (powerRawRun pBits n).1).2)).length ≤ _
      simp only [List.length_cons, List.length_append]
      calc
        _ ≤ (2 + n * (1 + 40 * (pBits.length + 1) *
              (pBits.length + 2 + 2 * limit * pBits.length))) +
            40 * (pBits.length + 1) * (pBits.length + 2 + 2 * limit * pBits.length) + 1 :=
          Nat.add_le_add_right (Nat.add_le_add hprev hstep) 1
        _ = _ := by ring

/-- A quadratic polynomial in both the iteration count and input bit length. -/
theorem powerRawRun_cost (pBits : List Bool) (n : ℕ) :
    (powerRawRun pBits n).2.length ≤
      2 + n * (1 + 40 * (pBits.length + 1) *
        (pBits.length + 2 + 2 * n * pBits.length)) :=
  powerRawRun_cost_le pBits n n le_rfl

/-- A single pass of exactly the requested output width. Each step inspects
an input cell and writes either its bit or a padding zero. -/
def normalizeRun : ℕ → List Bool → List Bool × List BitEvent
  | 0, _ => ([], [.control])
  | B + 1, [] =>
      let next := normalizeRun B []
      (false :: next.1, [.control, .inspect, .push] ++ next.2)
  | B + 1, b :: bs =>
      let next := normalizeRun B bs
      (b :: next.1, [.control, .inspect, .push] ++ next.2)

theorem normalizeRun_eq (B : ℕ) (xs : List Bool) :
    (normalizeRun B xs).1 = SubexpLiftRing.normalizeBits B xs := by
  induction B generalizing xs with
  | zero => simp [normalizeRun, SubexpLiftRing.normalizeBits, ModularArithmetic.padTo]
  | succ B ih =>
      cases xs <;>
        simp [normalizeRun, ih, SubexpLiftRing.normalizeBits,
          ModularArithmetic.padTo, List.replicate_succ]

@[simp] theorem normalizeRun_length (B : ℕ) (xs : List Bool) :
    (normalizeRun B xs).1.length = B := by
  rw [normalizeRun_eq, SubexpLiftRing.normalizeBits_length]

@[simp] theorem normalizeRun_cost (B : ℕ) (xs : List Bool) :
    (normalizeRun B xs).2.length = 3 * B + 1 := by
  induction B generalizing xs with
  | zero => simp [normalizeRun]
  | succ B ih =>
      cases xs <;> simp [normalizeRun, ih] <;> omega

theorem normalizeRun_value (B : ℕ) (xs : List Bool) (hx : BinaryArithmetic.toNat xs < 2 ^ B) :
    BinaryArithmetic.toNat (normalizeRun B xs).1 = BinaryArithmetic.toNat xs := by
  rw [normalizeRun_eq]
  exact SubexpLiftRing.normalizeBits_value B xs hx

/-- The raw arithmetic value fits in the linear target width, including n=0. -/
theorem power_lt_capacity (pBits : List Bool) (n : ℕ) :
    BinaryArithmetic.toNat pBits ^ n < 2 ^ (1 + n * pBits.length) := by
  calc
    BinaryArithmetic.toNat pBits ^ n ≤ (2 ^ pBits.length) ^ n :=
      Nat.pow_le_pow_left (Nat.le_of_lt (ModularArithmetic.toNat_lt_pow_length pBits)) n
    _ = 2 ^ (n * pBits.length) := by rw [← pow_mul, Nat.mul_comm pBits.length n]
    _ < 2 ^ (1 + n * pBits.length) := by
      rw [pow_add]
      have hp := Nat.two_pow_pos (n * pBits.length)
      norm_num

/-- Modulus construction followed by one traced canonical-width pass.
Only the width counter is calculated arithmetically; encoded values are
multiplied exclusively by the Boolean/list implementation. -/
def powerRun (pBits : List Bool) (n : ℕ) : List Bool × List BitEvent :=
  let raw := powerRawRun pBits n
  let out := normalizeRun (1 + n * pBits.length) raw.1
  (out.1, raw.2 ++ out.2)

theorem powerRun_value (pBits : List Bool) (n : ℕ) :
    BinaryArithmetic.toNat (powerRun pBits n).1 = BinaryArithmetic.toNat pBits ^ n := by
  unfold powerRun
  dsimp only
  rw [normalizeRun_value, powerRawRun_value]
  rw [powerRawRun_value]
  exact power_lt_capacity pBits n

@[simp] theorem powerRun_length (pBits : List Bool) (n : ℕ) :
    (powerRun pBits n).1.length = 1 + n * pBits.length := by
  exact normalizeRun_length _ _

theorem powerRun_length_le (pBits : List Bool) (n : ℕ) :
    (powerRun pBits n).1.length ≤ 1 + n * (pBits.length + 1) := by
  rw [powerRun_length]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left n (Nat.le_succ _)) 1

/-- Every multiplication trace and the final normalization trace are included. -/
theorem powerRun_cost (pBits : List Bool) (n : ℕ) :
    (powerRun pBits n).2.length ≤
      (2 + n * (1 + 40 * (pBits.length + 1) *
        (pBits.length + 2 + 2 * n * pBits.length))) +
          (3 * (1 + n * pBits.length) + 1) := by
  simp only [powerRun, List.length_append, normalizeRun_cost]
  exact Nat.add_le_add_right (powerRawRun_cost pBits n) _

/-- A compact uniform polynomial bound for the complete bit-event trace. -/
theorem powerRun_cost_quadratic (pBits : List Bool) (n : ℕ) :
    (powerRun pBits n).2.length ≤
      100 * (n + 1) ^ 2 * (pBits.length + 1) ^ 2 := by
  let b := pBits.length
  let q := (n + 1) * (b + 1)
  have hc := powerRun_cost pBits n
  change (powerRun pBits n).2.length ≤
    (2 + n * (1 + 40 * (b + 1) * (b + 2 + 2 * n * b))) +
      (3 * (1 + n * b) + 1) at hc
  have hq : 1 ≤ q := by dsimp [q]; nlinarith
  have hn : n ≤ q := by dsimp [q]; nlinarith
  have hw : 1 + n * b ≤ q := by dsimp [q]; nlinarith
  have hnb : n * (b + 1) ≤ q := by dsimp [q]; nlinarith
  have ht : b + 2 + 2 * n * b ≤ 2 * q := by dsimp [q]; nlinarith
  have hm := Nat.mul_le_mul hnb ht
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hout : (powerRun pBits n).2.length ≤ 100 * q ^ 2 := by nlinarith
  simpa [q, b, mul_pow, Nat.mul_assoc] using hout

/-- Fixed-width little-endian words are determined by their numeric value. -/
theorem bits_eq_of_length_of_value (xs ys : List Bool)
    (hlen : xs.length = ys.length) (hval : BinaryArithmetic.toNat xs = BinaryArithmetic.toNat ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      have hy : ys = [] := List.length_eq_zero_iff.mp hlen.symm
      exact hy.symm
  | cons b bs ih =>
      cases ys with
      | nil => simp at hlen
      | cons c cs =>
          have hb : b = c := by
            cases b <;> cases c <;> simp_all [toNat_cons] <;> omega
          subst c
          have ht : BinaryArithmetic.toNat bs = BinaryArithmetic.toNat cs := by
            simp only [toNat_cons] at hval
            omega
          exact congrArg (List.cons b) (ih cs (Nat.succ.inj hlen) ht)

/-- Characterization of the output, not an implementation by natural powers. -/
theorem powerRun_eq_fixedBits (pBits : List Bool) (n : ℕ) :
    (powerRun pBits n).1 =
      SubexpLiftRing.fixedBits (1 + n * pBits.length) (BinaryArithmetic.toNat pBits ^ n) := by
  apply bits_eq_of_length_of_value
  · rw [powerRun_length, SubexpLiftRing.fixedBits_length]
  · rw [powerRun_value, SubexpLiftRing.toNat_fixedBits_of_lt _ _ (power_lt_capacity pBits n)]

/-- With the standard prime word as input, the result is exactly the modulus
word previously specified by evaluating p^μ as a natural number. -/
theorem modulus_eq_fixedBits (p μ : ℕ) (pBits : List Bool)
    (hvalue : BinaryArithmetic.toNat pBits = p) (hwidth : pBits.length = Nat.log 2 p + 1) :
    (powerRun pBits μ).1 =
      SubexpLiftRing.fixedBits (SubexpLiftRing.baseWidth p μ + 1) (p ^ μ) := by
  simpa only [hvalue, hwidth, SubexpLiftRing.baseWidth, Nat.add_comm] using
    powerRun_eq_fixedBits pBits μ

theorem modulus_value (p μ : ℕ) (pBits : List Bool) (hvalue : BinaryArithmetic.toNat pBits = p) :
    BinaryArithmetic.toNat (powerRun pBits μ).1 = p ^ μ := by
  simpa only [hvalue] using powerRun_value pBits μ

theorem modulus_length (p μ : ℕ) (pBits : List Bool)
    (hwidth : pBits.length = Nat.log 2 p + 1) :
    (powerRun pBits μ).1.length = SubexpLiftRing.baseWidth p μ + 1 := by
  simp only [powerRun_length, hwidth, SubexpLiftRing.baseWidth, Nat.add_comm]

end SubexponentialSAT.SubexpModulusConstruction

end OAI.Algorithms
