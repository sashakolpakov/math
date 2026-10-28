import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchBasic

namespace OAI.Algorithms

/-!
# Explicit companion recurrence for the supplied monic polynomial

This module supplies the structure constants needed by the dynamic ring
program. It executes only coefficient-vector operations; polynomial
remainder is used solely to state and prove its meaning.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open Polynomial

def mulX {R : Type*} [Ring R] {d : ℕ} (c a : Fin d → R) : Fin d → R :=
  fun i => (if i.val = 0 then 0 else entry a (i.val - 1)) - entry a (d - 1) * c i

def oneVector {R : Type*} [Zero R] [One R] (d : ℕ) : Fin d → R :=
  fun i => if i.val = 0 then 1 else 0

/-- Materialize every coefficient before the next companion step. -/
def cacheVector {R : Type*} {d : ℕ} (a : Fin d → R) : Fin d → R :=
  let stored := List.Vector.ofFn a
  stored.get

@[simp] theorem cacheVector_eq {R : Type*} {d : ℕ} (a : Fin d → R) :
    cacheVector a = a := by
  funext i
  exact List.Vector.get_ofFn a i

def powerVector {R : Type*} [Ring R] {d : ℕ} (c : Fin d → R) : ℕ → (Fin d → R)
  | 0 => cacheVector (oneVector d)
  | n + 1 => cacheVector (mulX c (powerVector c n))

def structureTable {R : Type*} [Ring R] {d : ℕ} (c : Fin d → R)
    (i j k : Fin d) : R := powerVector c (i.val + j.val) k

section Correctness

variable {R : Type*} [CommRing R] [Nontrivial R] [DecidableEq R]
variable {d : ℕ} (hd : 0 < d) (c a : Fin d → R)
include hd

omit [Nontrivial R] in
theorem ofFn_mulX :
    Polynomial.ofFn d (mulX c a) = X * Polynomial.ofFn d a -
      C (entry a (d - 1)) * QuarticSearch.poly c := by
  apply Polynomial.ext
  intro j
  rw [coeff_sub, coeff_C_mul]
  cases j with
  | zero =>
      rw [coeff_X_mul_zero, ← candidateEntry_eq_coeff]
      simp [ entry, mulX, candidateEntry, hd,
        show (0 : ℕ) ≠ d by omega]
  | succ j =>
      rw [coeff_X_mul, ← candidateEntry_eq_coeff]
      by_cases hj : j + 1 < d
      · have hj0 : j < d := by omega
        simp [ entry, mulX, candidateEntry, hj, hj0,
          show j + 1 ≠ d by omega]
      · by_cases he : j + 1 = d
        · have hj0 : j < d := by omega
          have hsub : d - 1 = j := by omega
          simp [ entry, candidateEntry, he, hsub, hj0]
        · have hj0 : ¬j < d := by omega
          simp [ofFn_coeff_entry, entry, candidateEntry, hj, hj0, he]

omit [Nontrivial R] in
theorem ofFn_oneVector : Polynomial.ofFn d (oneVector (R := R) d) = 1 := by
  apply Polynomial.ext
  intro j
  by_cases hj : j = 0
  · subst j
    simp [ oneVector, hd]
  · by_cases hlt : j < d
    · simp [ oneVector, hlt, hj, coeff_one]
    · simp [ofFn_coeff_entry, entry, hlt, hj, coeff_one]

omit [Nontrivial R] in
theorem polynomial_dvd_power_sub_ofFn (n : ℕ) :
    QuarticSearch.poly c ∣ X ^ n - Polynomial.ofFn d (powerVector c n) := by
  induction n with
  | zero => simp [powerVector, ofFn_oneVector hd]
  | succ n ih =>
      rw [powerVector, cacheVector_eq, ofFn_mulX hd c]
      have he : X ^ (n + 1) - (X * Polynomial.ofFn d (powerVector c n) -
          C (entry (powerVector c n) (d - 1)) * QuarticSearch.poly c) =
          X * (X ^ n - Polynomial.ofFn d (powerVector c n)) +
            C (entry (powerVector c n) (d - 1)) * QuarticSearch.poly c := by
        rw [pow_succ]
        ring
      rw [he]
      exact dvd_add (dvd_mul_of_dvd_right ih X) (dvd_mul_left _ _)

theorem ofFn_powerVector (n : ℕ) :
    Polynomial.ofFn d (powerVector c n) = X ^ n %ₘ QuarticSearch.poly c := by
  have he := Polynomial.modByMonic_eq_of_dvd_sub (QuarticSearch.poly_monic c)
    (polynomial_dvd_power_sub_ofFn hd c n)
  have hlt : (Polynomial.ofFn d (powerVector c n)).degree < (QuarticSearch.poly c).degree := by
    rw [degree_eq_natDegree (QuarticSearch.poly_monic c).ne_zero, QuarticSearch.poly_natDegree]
    exact Polynomial.ofFn_degree_lt _
  rw [(Polynomial.modByMonic_eq_self_iff (QuarticSearch.poly_monic c)).mpr hlt] at he
  exact he.symm

theorem structureTable_eq_coeff (i j k : Fin d) :
    structureTable c i j k = (X ^ (i.val + j.val) %ₘ QuarticSearch.poly c).coeff k.val := by
  rw [← ofFn_powerVector hd c]
  exact (Polynomial.ofFn_coeff_eq_val_of_lt _ k.isLt).symm

end Correctness

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
