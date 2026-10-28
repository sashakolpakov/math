import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpResiduePolynomialInverse

namespace OAI.Algorithms

/-! One-accumulator Horner form of the truncated geometric series. This is
the state invariant used by the repeated physical multiply/add controller. -/

namespace SubexponentialSAT.SubexpPolynomialSeriesAlgebra

open Polynomial
open scoped BigOperators

variable {S A : Type*} [CommRing A]

theorem horner_denote (D : ℕ) (zero one z : S) (add mul : S → S → S)
    (denote : S → A[X]) (Z : A[X])
    (hzero : denote zero = 0) (hone : denote one = Truncation.trunc D 1)
    (hz : denote z = Truncation.trunc D Z)
    (hadd : ∀ x y, denote (add x y) = denote x + denote y)
    (hmul : ∀ x y, denote (mul x y) = Truncation.trunc D (denote x * denote y))
    (n : ℕ) :
    denote (((fun acc => add (mul acc z) one)^[n]) zero) =
      Truncation.trunc D (∑ j ∈ Finset.range n, Z ^ j) := by
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
      rw [Function.iterate_succ_apply', hadd, hmul, hz, ih,
        SubexpTruncatedGeometric.trunc_mul_trunc, hone, ← Truncation.trunc_add,
        geom_sum_succ]
      congr 1
      ring

theorem inverse_horner_denote (D μ : ℕ) (zero one z cb : S) (add mul : S → S → S)
    (denote : S → A[X]) (P : A[X]) (b : A)
    (hzero : denote zero = 0) (hone : denote one = Truncation.trunc D 1)
    (hz : denote z = Truncation.trunc D (1 - C b * P))
    (hcb : denote cb = Truncation.trunc D (C b))
    (hadd : ∀ x y, denote (add x y) = denote x + denote y)
    (hmul : ∀ x y, denote (mul x y) = Truncation.trunc D (denote x * denote y)) :
    denote (mul cb (((fun acc => add (mul acc z) one)^[D + μ]) zero)) =
      SubexpResiduePolynomialInverse.inverse P b D μ := by
  rw [hmul, hcb, horner_denote D zero one z add mul denote _ hzero hone hz hadd hmul,
    SubexpTruncatedGeometric.trunc_mul_trunc]
  rfl

/-- The actual local correction may use a residue seed and a longer
polynomial loop; its polynomial is the same correction as in the CRT proof. -/
theorem correction_horner_denote (D μ : ℕ) (zero one z cb jet : S)
    (add mul : S → S → S) (denote : S → A[X]) (P J : A[X]) (a b : A)
    (hzero : denote zero = 0) (hone : denote one = Truncation.trunc D 1)
    (hz : denote z = Truncation.trunc D (1 - C b * P))
    (hcb : denote cb = Truncation.trunc D (C b)) (hjet : denote jet = J)
    (hadd : ∀ x y, denote (add x y) = denote x + denote y)
    (hmul : ∀ x y, denote (mul x y) = Truncation.trunc D (denote x * denote y))
    (ha : a * P.coeff 0 = 1) (hb : (1 - b * P.coeff 0) ^ μ = 0) :
    denote (mul jet (mul cb (((fun acc => add (mul acc z) one)^[D + μ]) zero))) =
      TruncatedInverse.correctedJet P J a D := by
  rw [hmul, hjet,
    inverse_horner_denote D μ zero one z cb add mul denote P b hzero hone hz hcb hadd hmul,
    SubexpResiduePolynomialInverse.inverse_eq P a b D μ ha hb]
  rfl

end SubexponentialSAT.SubexpPolynomialSeriesAlgebra

end OAI.Algorithms
