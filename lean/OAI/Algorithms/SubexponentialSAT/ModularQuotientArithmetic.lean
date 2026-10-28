import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ModularArithmetic

namespace OAI.Algorithms

/-!
# The quotient bits emitted by binary long division

These bit/list functions specify the output of the finite division program.
Each quotient bit is the complement of the actual subtraction borrow; neither
the recurrence nor the bit selector calls natural-number division.
-/

namespace SubexponentialSAT.ModularQuotientArithmetic

open SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularArithmetic

def quotientBit (m r : List Bool) (b : Bool) : Bool :=
  !(subCarry false (b :: r) (padTo (b :: r) m)).2

/-- Return the little-endian quotient and padded remainder, in that order. -/
def divide (m : List Bool) : List Bool → List Bool × List Bool
  | [] => ([], padTo m [])
  | b :: bs =>
      let qr := divide m bs
      (quotientBit m qr.2 b :: qr.1, shiftReduce m qr.2 b)

@[simp] theorem divide_nil (m : List Bool) : divide m [] = ([], padTo m []) := rfl

@[simp] theorem divide_cons (m : List Bool) (b : Bool) (bs : List Bool) :
    divide m (b :: bs) =
      (quotientBit m (divide m bs).2 b :: (divide m bs).1,
        shiftReduce m (divide m bs).2 b) := rfl

@[simp] theorem divide_remainder (m xs : List Bool) :
    (divide m xs).2 = reduce m xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [reduce, ih]

@[simp] theorem divide_quotient_length (m xs : List Bool) :
    (divide m xs).1.length = xs.length := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [ih]

@[simp] theorem divide_remainder_length (m xs : List Bool) :
    (divide m xs).2.length = m.length + xs.length := by
  rw [divide_remainder, reduce_length]

/-- One subtraction records exactly the multiple of the modulus removed. -/
theorem quotientBit_step (m r : List Bool) (b : Bool) (hlen : m.length ≤ r.length) :
    BinaryArithmetic.toNat (b :: r) =
      BinaryArithmetic.toNat m * bitVal (quotientBit m r b) + BinaryArithmetic.toNat (shiftReduce m r b) := by
  have hp : BinaryArithmetic.toNat (padTo (b :: r) m) = BinaryArithmetic.toNat m :=
    padTo_correct _ _ (by simp only [List.length_cons]; omega)
  have hv := subCarry_correct false (b :: r) (padTo (b :: r) m)
    (padTo_length _ _).symm
  cases hb : (subCarry false (b :: r) (padTo (b :: r) m)).2 with
  | false =>
      simpa [quotientBit, shiftReduce, hb, hp] using hv
  | true => simp [quotientBit, shiftReduce, hb]

/-- The division identity itself only requires words, including a zero modulus. -/
theorem divide_identity (m xs : List Bool) :
    BinaryArithmetic.toNat xs = BinaryArithmetic.toNat m * BinaryArithmetic.toNat (divide m xs).1 + BinaryArithmetic.toNat (divide m xs).2 := by
  induction xs with
  | nil => simp [padTo_correct m [] (Nat.zero_le _)]
  | cons b bs ih =>
      have hl : m.length ≤ (divide m bs).2.length := by
        rw [divide_remainder_length]
        omega
      have hs := quotientBit_step m (divide m bs).2 b hl
      simp only [divide_cons, toNat_cons ] at hs ⊢
      rw [ih]
      nlinarith

theorem divide_remainder_correct (m xs : List Bool) (hm : 0 < BinaryArithmetic.toNat m) :
    BinaryArithmetic.toNat (divide m xs).2 = BinaryArithmetic.toNat xs % BinaryArithmetic.toNat m := by
  rw [divide_remainder, reduce_correct m xs hm]

theorem divide_remainder_lt (m xs : List Bool) (hm : 0 < BinaryArithmetic.toNat m) :
    BinaryArithmetic.toNat (divide m xs).2 < BinaryArithmetic.toNat m := by
  rw [divide_remainder_correct m xs hm]
  exact Nat.mod_lt _ hm

theorem divide_quotient_correct (m xs : List Bool) (hm : 0 < BinaryArithmetic.toNat m) :
    BinaryArithmetic.toNat (divide m xs).1 = BinaryArithmetic.toNat xs / BinaryArithmetic.toNat m := by
  have hi := divide_identity m xs
  have hr := divide_remainder_lt m xs hm
  conv_rhs => rw [hi]
  rw [Nat.mul_add_div hm, Nat.div_eq_of_lt hr, Nat.add_zero]

theorem divide_correct (m xs : List Bool) (hm : 0 < BinaryArithmetic.toNat m) :
    BinaryArithmetic.toNat (divide m xs).1 = BinaryArithmetic.toNat xs / BinaryArithmetic.toNat m ∧
    BinaryArithmetic.toNat (divide m xs).2 = BinaryArithmetic.toNat xs % BinaryArithmetic.toNat m ∧
    BinaryArithmetic.toNat (divide m xs).2 < BinaryArithmetic.toNat m ∧
    (divide m xs).1.length = xs.length ∧
    (divide m xs).2.length = m.length + xs.length :=
  ⟨divide_quotient_correct m xs hm, divide_remainder_correct m xs hm,
    divide_remainder_lt m xs hm, divide_quotient_length m xs,
    divide_remainder_length m xs⟩

end SubexponentialSAT.ModularQuotientArithmetic

end OAI.Algorithms
