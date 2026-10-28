import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentProgramCore

namespace OAI.Algorithms

/-! A direct H-adic multiplication table.  Entries are small integers computed
from bounded indices. No polynomial division or choice of a polynomial normal
form occurs in these executable definitions. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open scoped BigOperators

variable {R : Type*} [CommRing R]

def hValue (x : R) : R := x * (x - 1) * (x - 2)

def hadicBasis (t : ℕ) (x : R) (i : Fin (3*t)) : R :=
  x ^ (i.val % 3) * hValue x ^ (i.val / 3)

/-- One explicitly indexed coefficient, omitted automatically past `3*t`. -/
def atomInteger (n : ℕ) (z : ℤ) {t : ℕ} (k : Fin (3*t)) : ℤ :=
  if k.val = n then z else 0

/-- Products of `X^a H^s`, with `a < 3`, need only the relations for X^3,X^4. -/
def hadicTable {t : ℕ} (i j k : Fin (3*t)) : ℤ :=
  let s := i.val / 3 + j.val / 3
  let a := i.val % 3 + j.val % 3
  if a < 3 then atomInteger (3*s+a) 1 k
  else if a = 3 then
    atomInteger (3*(s+1)) 1 k + atomInteger (3*s+1) (-2) k +
      atomInteger (3*s+2) 3 k
  else
    atomInteger (3*(s+1)) 3 k + atomInteger (3*(s+1)+1) 1 k +
      atomInteger (3*s+1) (-6) k + atomInteger (3*s+2) 7 k

theorem hValue_pow_eq_zero (x : R) {t s : ℕ} (ht : hValue x ^ t = 0)
    (hs : t ≤ s) : hValue x ^ s = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [pow_add, ht, zero_mul]

theorem atomInteger_eval (t s a : ℕ) (z : ℤ) (x : R)
    (ha : a < 3) (ht : hValue x ^ t = 0) :
    (∑ k : Fin (3*t), (atomInteger (3*s+a) z k : R) * hadicBasis t x k) =
      (z : R) * (x^a * hValue x^s) := by
  by_cases hs : s < t
  · let k : Fin (3*t) := ⟨3*s+a, by omega⟩
    have hkmod : k.val % 3 = a := by dsimp [k]; omega
    have hkdiv : k.val / 3 = s := by dsimp [k]; omega
    calc
      (∑ j : Fin (3*t), (atomInteger (3*s+a) z j : R) * hadicBasis t x j) =
          (atomInteger (3*s+a) z k : R) * hadicBasis t x k := by
        apply Finset.sum_eq_single k
        · intro b _ hbk
          have hb : b.val ≠ 3*s+a := by
            intro hb
            apply hbk
            apply Fin.ext
            exact hb
          simp [atomInteger, hb]
        · simp
      _ = _ := by simp [atomInteger, hadicBasis, k, hkmod, hkdiv]
  · have hz := hValue_pow_eq_zero x ht (by omega : t ≤ s)
    rw [hz, mul_zero, mul_zero]
    apply Finset.sum_eq_zero
    intro k _
    have hk : k.val ≠ 3*s+a := by have := k.isLt; omega
    simp [atomInteger, hk]

theorem hadicBasis_mul (t : ℕ) (x : R) (i j : Fin (3*t)) :
    hadicBasis t x i * hadicBasis t x j =
      x^(i.val%3+j.val%3) * hValue x^(i.val/3+j.val/3) := by
  simp only [hadicBasis, pow_add]
  ring

theorem hadicTable_correct (t : ℕ) (x : R) (ht : hValue x ^ t = 0)
    (i j : Fin (3*t)) :
    hadicBasis t x i * hadicBasis t x j =
      ∑ k : Fin (3*t), (hadicTable i j k : R) * hadicBasis t x k := by
  rw [hadicBasis_mul]
  let s := i.val / 3 + j.val / 3
  let a := i.val % 3 + j.val % 3
  have ha : a ≤ 4 := by dsimp [a]; omega
  change x^a * hValue x^s = _
  by_cases ha3 : a < 3
  · simp only [hadicTable, show i.val/3+j.val/3 = s from rfl,
      show i.val%3+j.val%3 = a from rfl, ha3, ↓reduceIte]
    rw [atomInteger_eval t s a 1 x ha3 ht]
    simp
  · by_cases heq : a = 3
    · simp only [hadicTable, show i.val/3+j.val/3 = s from rfl,
        show i.val%3+j.val%3 = a from rfl, heq, Nat.lt_irrefl, ↓reduceIte,
        Int.cast_add, add_mul, Finset.sum_add_distrib]
      rw [show 3*(s+1) = 3*(s+1)+0 by omega,
        atomInteger_eval t (s+1) 0 1 x (by omega) ht,
        atomInteger_eval t s 1 (-2) x (by omega) ht,
        atomInteger_eval t s 2 3 x (by omega) ht]
      simp only [ Int.cast_one, Int.cast_neg, Int.cast_ofNat, pow_zero, one_mul]
      rw [pow_succ]
      unfold hValue
      ring
    · have heq4 : a = 4 := by omega
      simp only [hadicTable, show i.val/3+j.val/3 = s from rfl,
        show i.val%3+j.val%3 = a from rfl, ha3, heq, ↓reduceIte,
        Int.cast_add, add_mul, Finset.sum_add_distrib]
      rw [show 3*(s+1) = 3*(s+1)+0 by omega,
        atomInteger_eval t (s+1) 0 3 x (by omega) ht,
        atomInteger_eval t (s+1) 1 1 x (by omega) ht,
        atomInteger_eval t s 1 (-6) x (by omega) ht,
        atomInteger_eval t s 2 7 x (by omega) ht]
      simp only [heq4, Int.cast_one, Int.cast_neg, Int.cast_ofNat, pow_zero, one_mul]
      rw [pow_succ]
      unfold hValue
      ring

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
