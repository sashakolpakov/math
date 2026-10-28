import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Tactic.Ring

/-! # Reversal Signs -/

namespace OAI.AlgebraicTopology.Products.ReversalSigns

/-!
# Signs for reversing simplex vertices

Reversing the `n+1` ordered vertices of an `n`-simplex has sign
`(-1)^(n*(n+1)/2)`. The integer signs below satisfy the exact face and
degree-splitting identities used by signed reversal of singular chains
and reversal of the cup product.
-/

/-- The number of pairs among the `n+1` ordered vertices. -/
def reversalExponent (n : ℕ) : ℕ := n * (n + 1) / 2

theorem reversalExponent_eq_choose (n : ℕ) :
    reversalExponent n = (n + 1).choose 2 := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel]
  unfold reversalExponent
  rw [Nat.mul_comm n (n + 1)]

@[simp]
theorem reversalExponent_zero : reversalExponent 0 = 0 := rfl

theorem reversalExponent_succ (n : ℕ) :
    reversalExponent (n + 1) = n + 1 + reversalExponent n := by
  rw [reversalExponent_eq_choose (n + 1), Nat.choose_succ_succ,
    Nat.choose_one_right, ← reversalExponent_eq_choose n]

theorem reversalExponent_add (p q : ℕ) :
    reversalExponent (p + q) = reversalExponent p + reversalExponent q + p * q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.add_succ, reversalExponent_succ, ih, reversalExponent_succ, Nat.mul_succ]
    omega

/-- The integer sign used to reverse an `n`-simplex. -/
def reversalSign (n : ℕ) : ℤ := (-1) ^ reversalExponent n

theorem reversalSign_eq (n : ℕ) : reversalSign n = (-1 : ℤ) ^ (n * (n + 1) / 2) := rfl

@[simp]
theorem reversalSign_zero : reversalSign 0 = 1 := rfl

/-- The sign gained by adding one vertex. -/
theorem reversalSign_succ (n : ℕ) :
    reversalSign (n + 1) = (-1 : ℤ) ^ (n + 1) * reversalSign n := by
  unfold reversalSign
  rw [reversalExponent_succ, pow_add]

/-- The degree-splitting identity for cup-product reversal. -/
theorem reversalSign_add (p q : ℕ) :
    reversalSign (p + q) = (-1 : ℤ) ^ (p * q) * reversalSign p * reversalSign q := by
  unfold reversalSign
  rw [reversalExponent_add, pow_add, pow_add]
  ring

@[simp]
theorem reversalSign_sq (n : ℕ) : reversalSign n ^ 2 = 1 := by
  unfold reversalSign
  rw [← pow_mul, Nat.mul_comm (reversalExponent n) 2, pow_mul, neg_one_sq, one_pow]

@[simp]
theorem reversalSign_mul_self (n : ℕ) : reversalSign n * reversalSign n = 1 := by
  simpa only [pow_two] using reversalSign_sq n

/-- The alternating face coefficient after reversing the vertices agrees
with signed reversal of the oppositely indexed face. -/
theorem reversalSign_face (n : ℕ) (i : Fin (n + 2)) :
    reversalSign (n + 1) * (-1 : ℤ) ^ i.val =
      reversalSign n * (-1 : ℤ) ^ i.rev.val := by
  have hi : n + 1 + i.val = i.rev.val + 2 * i.val := by
    rw [Fin.val_rev]
    omega
  calc
    reversalSign (n + 1) * (-1 : ℤ) ^ i.val =
        reversalSign n * ((-1 : ℤ) ^ (n + 1) * (-1 : ℤ) ^ i.val) := by
      rw [reversalSign_succ]
      ring
    _ = reversalSign n * (-1 : ℤ) ^ (n + 1 + i.val) := by rw [← pow_add]
    _ = reversalSign n * (-1 : ℤ) ^ (i.rev.val + 2 * i.val) := by rw [hi]
    _ = reversalSign n * (-1 : ℤ) ^ i.rev.val := by
      rw [pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

theorem reversalSign_face_rev (n : ℕ) (i : Fin (n + 2)) :
    reversalSign (n + 1) * (-1 : ℤ) ^ i.rev.val =
      reversalSign n * (-1 : ℤ) ^ i.val := by
  simpa only [Fin.rev_rev] using reversalSign_face n i.rev

variable (R : Type*) [CommRing R]

/-- Casting the integer sign gives the same power of negative one. -/
theorem reversalSign_cast (n : ℕ) :
    (reversalSign n : R) = (-1 : R) ^ (n * (n + 1) / 2) := by
  simp only [reversalSign_eq, Int.cast_pow, Int.cast_neg, Int.cast_one]

@[simp]
theorem reversalSign_cast_zero : (reversalSign 0 : R) = 1 := by
  rw [reversalSign_zero, Int.cast_one]

theorem reversalSign_cast_succ (n : ℕ) :
    (reversalSign (n + 1) : R) = (-1 : R) ^ (n + 1) * (reversalSign n : R) := by
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] using
    congrArg (fun z : ℤ => (z : R)) (reversalSign_succ n)

theorem reversalSign_cast_add (p q : ℕ) :
    (reversalSign (p + q) : R) =
      (-1 : R) ^ (p * q) * (reversalSign p : R) * (reversalSign q : R) := by
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] using
    congrArg (fun z : ℤ => (z : R)) (reversalSign_add p q)

@[simp]
theorem reversalSign_cast_sq (n : ℕ) : (reversalSign n : R) ^ 2 = 1 := by
  simpa only [Int.cast_pow, Int.cast_one] using
    congrArg (fun z : ℤ => (z : R)) (reversalSign_sq n)

@[simp]
theorem reversalSign_cast_mul_self (n : ℕ) :
    (reversalSign n : R) * (reversalSign n : R) = 1 := by
  simpa only [pow_two] using reversalSign_cast_sq R n

theorem reversalSign_cast_face (n : ℕ) (i : Fin (n + 2)) :
    (reversalSign (n + 1) : R) * (-1 : R) ^ i.val =
      (reversalSign n : R) * (-1 : R) ^ i.rev.val := by
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one] using
    congrArg (fun z : ℤ => (z : R)) (reversalSign_face n i)

theorem reversalSign_cast_face_rev (n : ℕ) (i : Fin (n + 2)) :
    (reversalSign (n + 1) : R) * (-1 : R) ^ i.rev.val =
      (reversalSign n : R) * (-1 : R) ^ i.val := by
  simpa only [Fin.rev_rev] using reversalSign_cast_face R n i.rev

end OAI.AlgebraicTopology.Products.ReversalSigns
