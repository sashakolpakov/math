import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.WalshExistenceSearch

namespace OAI.Algorithms

/-! Walsh testing using a mod-two matrix product and natural-number counters. -/
namespace SubexponentialSAT.SqrtLog.WalshExistence

open scoped BigOperators
open Cayley

def parityProducts {r D : ℕ} (s : Fin D → Cube r) (a : Cube r) : Fin D → ZMod 2 :=
  fun i => ∑ j, s i j * a j

def parityWeight {r D : ℕ} (s : Fin D → Cube r) (a : Cube r) : ℕ :=
  (Finset.univ.filter (fun i => parityProducts s a i ≠ 0)).card

theorem bitSign_sum {ι : Type*} (t : Finset ι) (f : ι → ZMod 2) :
    bitSign (∑ i ∈ t, f i) = ∏ i ∈ t, bitSign (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih => simp [hi, bitSign_add, ih]

theorem character_parity {r D : ℕ} (s : Fin D → Cube r) (a : Cube r) (i : Fin D) :
    character a (s i) = bitSign (parityProducts s a i) := by
  unfold character parityProducts
  rw [bitSign_sum]
  apply Finset.prod_congr rfl
  intro j _
  rw [mul_comm]

theorem characterInt_parity {r D : ℕ} (s : Fin D → Cube r) (a : Cube r) (i : Fin D) :
    characterInt a (s i) = 1 - 2 * (if parityProducts s a i ≠ 0 then (1 : ℤ) else 0) := by
  apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℝ)))
  push_cast
  rw [characterInt_cast, character_parity]
  by_cases h : parityProducts s a i = 0 <;> norm_num [bitSign, h]

theorem walshInt_eq_sub_twice_weight {r D : ℕ} (s : Fin D → Cube r) (a : Cube r) :
    walshInt s a = (D : ℤ) - 2 * parityWeight s a := by
  unfold walshInt
  simp_rw [characterInt_parity]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hh : (∑ i : Fin D, if parityProducts s a i ≠ 0 then (1 : ℤ) else 0) =
      parityWeight s a := by
    rw [← Finset.sum_filter]
    simp [parityWeight]
  rw [hh]
  simp

theorem int_abs_bound_iff_nat_checks (q D h : ℕ) :
    (q : ℤ) * |(D : ℤ) - 2 * h| ≤ D ↔
      q * D ≤ D + 2 * q * h ∧ 2 * q * h ≤ q * D + D := by
  have he : |(q : ℤ) * ((D : ℤ) - 2 * h)| = (q : ℤ) * |(D : ℤ) - 2 * h| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg q)]
  rw [← he, abs_le]
  constructor
  · rintro ⟨hl, hu⟩
    have h1 : (q : ℤ) * D ≤ D + 2 * q * h := by nlinarith
    have h2 : (2 : ℤ) * q * h ≤ q * D + D := by nlinarith
    exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  · rintro ⟨h1, h2⟩
    have h1' : (q : ℤ) * D ≤ D + 2 * q * h := by exact_mod_cast h1
    have h2' : (2 : ℤ) * q * h ≤ q * D + D := by exact_mod_cast h2
    constructor <;> nlinarith

theorem good_iff_parity_checks {r D : ℕ} (q : ℕ) (s : Fin D → Cube r) :
    Good q s ↔ ∀ a, a ≠ 0 →
      q * D ≤ D + 2 * q * parityWeight s a ∧
        2 * q * parityWeight s a ≤ q * D + D := by
  unfold Good
  simp_rw [walshInt_eq_sub_twice_weight, int_abs_bound_iff_nat_checks]

end SubexponentialSAT.SqrtLog.WalshExistence

end OAI.Algorithms
