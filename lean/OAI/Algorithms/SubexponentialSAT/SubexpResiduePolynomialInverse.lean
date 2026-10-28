import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpTruncatedGeometric
import OAI.Algorithms.SubexponentialSAT.SubexpResidueInverse

namespace OAI.Algorithms

/-! Local inversion directly from a residue-field Fermat seed. A scalar
inverse in the lifted ring is unnecessary: D+μ polynomial geometric steps
annihilate both the nilpotent constant defect and the positive-degree part.
All intermediate products may still be truncated to D coefficients. -/

namespace SubexponentialSAT.SubexpResiduePolynomialInverse

open Polynomial
open scoped BigOperators

variable {A : Type*} [CommRing A]

theorem defect_power_dvd (P : A[X]) (b : A) (D μ : ℕ)
    (hconstant : (1 - b * P.coeff 0) ^ μ = 0) :
    (X : A[X]) ^ D ∣ (1 - C b * P) ^ (D + μ) := by
  let z : A[X] := 1 - C b * P
  let c : A[X] := C (1 - b * P.coeff 0)
  have hx : (X : A[X]) ∣ z - c := by
    apply X_dvd_iff.mpr
    simp [z, c, coeff_sub]
  have hc : c ^ μ = 0 := by
    dsimp [c]
    rw [← map_pow, hconstant, map_zero]
  have hpow : (X : A[X]) ^ D ∣ ((z - c) + c) ^ (D + μ) := by
    rw [add_pow]
    apply Finset.dvd_sum
    intro k hk
    by_cases hDk : D ≤ k
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
        ((pow_dvd_pow_of_dvd hx D).trans (pow_dvd_pow (z - c) hDk)) _) _
    · have hμ : μ ≤ D + μ - k := by omega
      rw [pow_eq_zero_of_le hμ hc, mul_zero, zero_mul]
      exact dvd_zero _
  simpa only [sub_add_cancel] using hpow

/-- D+μ terms suffice for a polynomial whose constant coefficient is
invertible modulo the nilpotent maximal ideal. -/
noncomputable def inverse (P : A[X]) (b : A) (D μ : ℕ) : A[X] :=
  Truncation.trunc D (TruncatedInverse.rawInverse P b (D + μ))

theorem inverse_correct (P : A[X]) (b : A) (D μ : ℕ)
    (hconstant : (1 - b * P.coeff 0) ^ μ = 0) :
    (X : A[X]) ^ D ∣ P * inverse P b D μ - 1 := by
  have hraw : (X : A[X]) ^ D ∣
      P * TruncatedInverse.rawInverse P b (D + μ) - 1 := by
    have heq : P * TruncatedInverse.rawInverse P b (D + μ) - 1 =
        -((1 - C b * P) ^ (D + μ)) := by
      calc
        P * TruncatedInverse.rawInverse P b (D + μ) - 1 =
            (1 - (1 - C b * P)) *
              (∑ j ∈ Finset.range (D + μ), (1 - C b * P) ^ j) - 1 := by
                dsimp [TruncatedInverse.rawInverse]
                ring
        _ = -((1 - C b * P) ^ (D + μ)) := by rw [mul_neg_geom_sum]; ring
    rw [heq]
    exact dvd_neg.mpr (defect_power_dvd P b D μ hconstant)
  have htail := dvd_mul_of_dvd_right
    (TruncatedInverse.X_pow_dvd_sub_trunc D (TruncatedInverse.rawInverse P b (D + μ))) P
  convert dvd_sub hraw htail using 1
  dsimp [inverse]
  ring

/-- Equality to the original CRT inverse follows from its uniqueness modulo
X^D, without running the exact scalar inverse algorithm. -/
theorem inverse_eq (P : A[X]) (a b : A) (D μ : ℕ)
    (ha : a * P.coeff 0 = 1) (hb : (1 - b * P.coeff 0) ^ μ = 0) :
    inverse P b D μ = TruncatedInverse.inverse P a D := by
  have h₁ := inverse_correct P b D μ hb
  have h₂ := TruncatedInverse.inverse_correct P a D ha
  have hd : (X : A[X]) ^ D ∣ inverse P b D μ - TruncatedInverse.inverse P a D := by
    convert dvd_sub
      (dvd_mul_of_dvd_right h₁ (TruncatedInverse.inverse P a D))
      (dvd_mul_of_dvd_right h₂ (inverse P b D μ)) using 1
    ring
  have hm := Polynomial.modByMonic_eq_of_dvd_sub (monic_X.pow D) hd
  rw [← TruncatedInverse.trunc_eq_modByMonic, ← TruncatedInverse.trunc_eq_modByMonic] at hm
  simpa only [inverse, TruncatedInverse.inverse, TruncatedInverse.trunc_idempotent] using hm

theorem inverse_from_loop {S : Type*}
    (D μ : ℕ) (zero one z cb : S) (add mul : S → S → S) (denote : S → A[X])
    (P : A[X]) (b : A)
    (hzero : denote zero = 0) (hone : denote one = Truncation.trunc D 1)
    (hz : denote z = Truncation.trunc D (1 - C b * P))
    (hcb : denote cb = Truncation.trunc D (C b))
    (hadd : ∀ x y, denote (add x y) = denote x + denote y)
    (hmul : ∀ x y, denote (mul x y) = Truncation.trunc D (denote x * denote y)) :
    denote (mul cb (TruncatedInverse.geometricLoop zero one add mul z (D + μ)).2) =
      inverse P b D μ := by
  rw [hmul, hcb,
    (SubexpTruncatedGeometric.geometricLoop_denote D zero one z add mul denote _
      hzero hone hz hadd hmul (D + μ)).2,
    SubexpTruncatedGeometric.trunc_mul_trunc]
  rfl

theorem fermat_inverse_correct {E : Type*} [Field E] [Fintype E]
    (ρ : A →+* E) (q : ℕ) (hq : Fintype.card E = q)
    (π : A) (μ : ℕ) (hπ : π ^ μ = 0) (hker : ∀ x, ρ x = 0 → π ∣ x)
    (P : A[X]) (hP : ρ (P.coeff 0) ≠ 0) (D : ℕ) :
    (X : A[X]) ^ D ∣ P * inverse P (P.coeff 0 ^ (q - 2)) D μ - 1 := by
  apply inverse_correct
  simpa only [mul_comm] using
    SubexpResidueInverse.fermat_defect_nilpotent ρ q hq π μ hπ hker (P.coeff 0) hP

theorem fermat_inverse_eq {E : Type*} [Field E] [Fintype E]
    (ρ : A →+* E) (q : ℕ) (hq : Fintype.card E = q)
    (π : A) (μ : ℕ) (hπ : π ^ μ = 0) (hker : ∀ x, ρ x = 0 → π ∣ x)
    (P : A[X]) (hP : ρ (P.coeff 0) ≠ 0) (a : A) (ha : a * P.coeff 0 = 1) (D : ℕ) :
    inverse P (P.coeff 0 ^ (q - 2)) D μ = TruncatedInverse.inverse P a D := by
  apply inverse_eq P a _ D μ ha
  simpa only [mul_comm] using
    SubexpResidueInverse.fermat_defect_nilpotent ρ q hq π μ hπ hker (P.coeff 0) hP

end SubexponentialSAT.SubexpResiduePolynomialInverse

end OAI.Algorithms
