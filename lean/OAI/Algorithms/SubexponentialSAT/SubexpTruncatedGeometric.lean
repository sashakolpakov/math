import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.TruncatedInverse

namespace OAI.Algorithms

/-! Keeping every geometric-inverse intermediate below degree D preserves
the existing inverse formula. The loop itself is the already executable
`TruncatedInverse.geometricLoop`; these are its semantic invariants. -/

namespace SubexponentialSAT.SubexpTruncatedGeometric

open Polynomial
open scoped BigOperators

variable {R : Type*} [CommRing R]

theorem trunc_mul_trunc (D : ℕ) (P Q : Polynomial R) :
    Truncation.trunc D (Truncation.trunc D P * Truncation.trunc D Q) =
      Truncation.trunc D (P * Q) := by
  have h₁ := dvd_mul_of_dvd_right (TruncatedInverse.X_pow_dvd_sub_trunc D P) Q
  have h₂ := dvd_mul_of_dvd_right (TruncatedInverse.X_pow_dvd_sub_trunc D Q)
    (Truncation.trunc D P)
  have h : (X : Polynomial R) ^ D ∣ P * Q - Truncation.trunc D P * Truncation.trunc D Q := by
    convert dvd_add h₁ h₂ using 1
    ring
  rw [TruncatedInverse.trunc_eq_modByMonic D (Truncation.trunc D P * Truncation.trunc D Q),
    TruncatedInverse.trunc_eq_modByMonic D (P * Q)]
  exact (Polynomial.modByMonic_eq_of_dvd_sub (monic_X.pow D) h).symm

theorem trunc_mul_trunc_right (D : ℕ) (P Q : Polynomial R) :
    Truncation.trunc D (P * Truncation.trunc D Q) = Truncation.trunc D (P * Q) := by
  have h := dvd_mul_of_dvd_right (TruncatedInverse.X_pow_dvd_sub_trunc D Q) P
  have h' : (X : Polynomial R) ^ D ∣ P * Q - P * Truncation.trunc D Q := by
    convert h using 1
    ring
  rw [TruncatedInverse.trunc_eq_modByMonic D (P * Truncation.trunc D Q),
    TruncatedInverse.trunc_eq_modByMonic D (P * Q)]
  exact (Polynomial.modByMonic_eq_of_dvd_sub (monic_X.pow D) h').symm

theorem geometricLoop_denote {S : Type*}
    (D : ℕ) (zero one z : S) (add mul : S → S → S) (denote : S → Polynomial R)
    (Z : Polynomial R)
    (hzero : denote zero = 0)
    (hone : denote one = Truncation.trunc D 1)
    (hz : denote z = Truncation.trunc D Z)
    (hadd : ∀ a b, denote (add a b) = denote a + denote b)
    (hmul : ∀ a b, denote (mul a b) = Truncation.trunc D (denote a * denote b))
    (n : ℕ) :
    denote (TruncatedInverse.geometricLoop zero one add mul z n).1 = Truncation.trunc D (Z ^ n) ∧
      denote (TruncatedInverse.geometricLoop zero one add mul z n).2 =
        Truncation.trunc D (∑ j ∈ Finset.range n, Z ^ j) := by
  induction n with
  | zero => simp [TruncatedInverse.geometricLoop, hzero, hone]
  | succ n ih =>
      constructor
      · simp only [TruncatedInverse.geometricLoop, hmul, ih.1, hz, trunc_mul_trunc, pow_succ]
      · simp only [TruncatedInverse.geometricLoop, hadd, ih.1, ih.2,
          Finset.sum_range_succ, Truncation.trunc_add]

/-- A D-step fixed-width loop followed by scalar multiplication returns
the same polynomial inverse used by the checked CRT reconstruction. -/
theorem inverse_from_loop {S : Type*}
    (D : ℕ) (zero one z : S) (add mul : S → S → S) (denote : S → Polynomial R)
    (P : Polynomial R) (a : R)
    (hzero : denote zero = 0)
    (hone : denote one = Truncation.trunc D 1)
    (hz : denote z = Truncation.trunc D (1 - C a * P))
    (hadd : ∀ x y, denote (add x y) = denote x + denote y)
    (hmul : ∀ x y, denote (mul x y) = Truncation.trunc D (denote x * denote y)) :
    Truncation.trunc D
      (C a * denote (TruncatedInverse.geometricLoop zero one add mul z D).2) =
        TruncatedInverse.inverse P a D := by
  rw [(geometricLoop_denote D zero one z add mul denote _ hzero hone hz hadd hmul D).2,
    trunc_mul_trunc_right]
  rfl

theorem inverse_from_loop_correct {S : Type*}
    (D : ℕ) (zero one z : S) (add mul : S → S → S) (denote : S → Polynomial R)
    (P : Polynomial R) (a : R)
    (hzero : denote zero = 0)
    (hone : denote one = Truncation.trunc D 1)
    (hz : denote z = Truncation.trunc D (1 - C a * P))
    (hadd : ∀ x y, denote (add x y) = denote x + denote y)
    (hmul : ∀ x y, denote (mul x y) = Truncation.trunc D (denote x * denote y))
    (ha : a * P.coeff 0 = 1) :
    (X : Polynomial R) ^ D ∣ P * Truncation.trunc D
      (C a * denote (TruncatedInverse.geometricLoop zero one add mul z D).2) - 1 := by
  rw [inverse_from_loop D zero one z add mul denote P a hzero hone hz hadd hmul]
  exact TruncatedInverse.inverse_correct P a D ha

end SubexponentialSAT.SubexpTruncatedGeometric

end OAI.Algorithms
