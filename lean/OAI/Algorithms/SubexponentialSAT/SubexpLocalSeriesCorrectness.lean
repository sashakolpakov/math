import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPolynomialSeriesAlgebra

namespace OAI.Algorithms

/-! Correctness of the exact operand order used by the physical local CRT
controller: Pt times the negative seed, then series times seed, then inverse
times jet. No commutativity of the represented operations is assumed. -/

namespace SubexponentialSAT.SubexpLocalSeriesCorrectness

open Polynomial
open scoped BigOperators

variable {S A : Type*} [CommRing A]

theorem defect_denote (D : ℕ) (pt negativeSeed one : S)
    (add mul : S → S → S) (denote : S → A[X]) (P : A[X]) (b : A)
    (hpt : denote pt = Truncation.trunc D P)
    (hnegative : denote negativeSeed = Truncation.trunc D (C (-b)))
    (hone : denote one = Truncation.trunc D 1)
    (hadd : ∀ x y, denote (add x y) = denote x + denote y)
    (hmul : ∀ x y, denote (mul x y) = Truncation.trunc D (denote x * denote y)) :
    denote (add (mul pt negativeSeed) one) = Truncation.trunc D (1 - C b * P) := by
  rw [hadd, hmul, hpt, hnegative, SubexpTruncatedGeometric.trunc_mul_trunc,
    hone, ← Truncation.trunc_add]
  congr 1
  rw [map_neg]
  ring

theorem inverse_denote (D μ : ℕ) (zero one z cb : S)
    (add mul : S → S → S) (denote : S → A[X]) (P : A[X]) (b : A)
    (hzero : denote zero = 0) (hone : denote one = Truncation.trunc D 1)
    (hz : denote z = Truncation.trunc D (1 - C b * P))
    (hcb : denote cb = Truncation.trunc D (C b))
    (hadd : ∀ x y, denote (add x y) = denote x + denote y)
    (hmul : ∀ x y, denote (mul x y) = Truncation.trunc D (denote x * denote y)) :
    denote (mul (((fun acc => add (mul acc z) one)^[D + μ]) zero) cb) =
      SubexpResiduePolynomialInverse.inverse P b D μ := by
  rw [hmul, hcb,
    SubexpPolynomialSeriesAlgebra.horner_denote D zero one z add mul denote _
      hzero hone hz hadd hmul,
    SubexpTruncatedGeometric.trunc_mul_trunc]
  change Truncation.trunc D (_ * C b) = Truncation.trunc D (C b * _)
  rw [mul_comm]

theorem correction_denote (D μ : ℕ) (zero one z cb jet : S)
    (add mul : S → S → S) (denote : S → A[X]) (P J : A[X]) (a b : A)
    (hzero : denote zero = 0) (hone : denote one = Truncation.trunc D 1)
    (hz : denote z = Truncation.trunc D (1 - C b * P))
    (hcb : denote cb = Truncation.trunc D (C b)) (hjet : denote jet = J)
    (hadd : ∀ x y, denote (add x y) = denote x + denote y)
    (hmul : ∀ x y, denote (mul x y) = Truncation.trunc D (denote x * denote y))
    (ha : a * P.coeff 0 = 1) (hb : (1 - b * P.coeff 0) ^ μ = 0) :
    denote (mul (mul (((fun acc => add (mul acc z) one)^[D + μ]) zero) cb) jet) =
      TruncatedInverse.correctedJet P J a D := by
  rw [hmul, hjet, inverse_denote D μ zero one z cb add mul denote P b
    hzero hone hz hcb hadd hmul, SubexpResiduePolynomialInverse.inverse_eq P a b D μ ha hb]
  unfold TruncatedInverse.correctedJet
  rw [mul_comm]

theorem correction_from_fermat {E : Type*} [Field E] [Fintype E]
    (ρ : A →+* E) (q : ℕ) (hq : Fintype.card E = q)
    (π : A) (μ : ℕ) (hπ : π ^ μ = 0) (hker : ∀ x, ρ x = 0 → π ∣ x)
    (D : ℕ) (zero one pt negativeSeed cb jet : S)
    (add mul : S → S → S) (denote : S → A[X]) (P J : A[X]) (a : A)
    (hP : ρ (P.coeff 0) ≠ 0) (ha : a * P.coeff 0 = 1)
    (hzero : denote zero = 0) (hone : denote one = Truncation.trunc D 1)
    (hpt : denote pt = Truncation.trunc D P)
    (hnegative : denote negativeSeed = Truncation.trunc D (C (-(P.coeff 0 ^ (q - 2)))))
    (hcb : denote cb = Truncation.trunc D (C (P.coeff 0 ^ (q - 2))))
    (hjet : denote jet = J)
    (hadd : ∀ x y, denote (add x y) = denote x + denote y)
    (hmul : ∀ x y, denote (mul x y) = Truncation.trunc D (denote x * denote y)) :
    let z := add (mul pt negativeSeed) one
    denote (mul (mul (((fun acc => add (mul acc z) one)^[D + μ]) zero) cb) jet) =
      TruncatedInverse.correctedJet P J a D := by
  intro z
  apply correction_denote D μ zero one z cb jet add mul denote P J a _
    hzero hone (defect_denote D pt negativeSeed one add mul denote P _ hpt hnegative hone hadd hmul)
    hcb hjet hadd hmul ha
  simpa only [mul_comm] using
    SubexpResidueInverse.fermat_defect_nilpotent ρ q hq π μ hπ hker (P.coeff 0) hP

end SubexponentialSAT.SubexpLocalSeriesCorrectness

end OAI.Algorithms
