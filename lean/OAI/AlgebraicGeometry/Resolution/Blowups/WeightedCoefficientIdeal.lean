import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.PowerOrder
import Mathlib.Data.Nat.Factorial.Basic

/-! # Weighted Coefficient Ideal -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.WeightedCoefficientIdeal.Construction

noncomputable section

/-! A single marked ideal representing a finite list of coefficient conditions. -/

/-- Exponent used to put the coefficient with control `b-j` at control `b!`. -/
def coefficientWeight (b : ℕ) (j : Fin b) : ℕ := b.factorial / (b - j.val)

theorem coefficientWeight_mul_control (b : ℕ) (j : Fin b) :
    (b - j.val) * coefficientWeight b j = b.factorial := by
  exact Nat.mul_div_cancel' (Nat.dvd_factorial (by omega) (Nat.sub_le b j.val))

theorem coefficientWeight_pos (b : ℕ) (j : Fin b) : 0 < coefficientWeight b j := by
  have h := coefficientWeight_mul_control b j
  have hp := Nat.factorial_pos b
  by_contra hn
  have hz : coefficientWeight b j = 0 := by omega
  rw [hz, Nat.mul_zero] at h
  omega

/-- The finite sum of powers of the coefficient ideals, at common control `b!`. -/
def weightedCoefficientIdeal {R : Type*} [CommRing R] (b : ℕ) (J : Fin b → Ideal R) :
    Ideal R := ⨆ j, J j ^ coefficientWeight b j

theorem weightedCoefficientIdeal_map {R T : Type*} [CommRing R] [CommRing T]
    (φ : R →+* T) (b : ℕ) (J : Fin b → Ideal R) :
    (weightedCoefficientIdeal b J).map φ = weightedCoefficientIdeal b (fun j => (J j).map φ) := by
  simp only [weightedCoefficientIdeal, Ideal.map_iSup, Ideal.map_pow]

/-- The coefficient bounds imply the common weighted bound for every ideal. -/
theorem weightedCoefficientIdeal_le_pow {R : Type*} [CommRing R]
    (M : Ideal R) (b : ℕ) (J : Fin b → Ideal R)
    (hJ : ∀ j, J j ≤ M ^ (b - j.val)) :
    weightedCoefficientIdeal b J ≤ M ^ b.factorial := by
  apply iSup_le
  intro j
  have h := pow_le_pow_left' (hJ j) (coefficientWeight b j)
  rwa [← pow_mul, coefficientWeight_mul_control] at h

variable {σ K S : Type*} [Field K] [IsAlgClosed K] [CommRing S] [Finite σ]
  [Algebra (MvPolynomial σ K) S] [Algebra.Etale (MvPolynomial σ K) S]

/-- On an actual étale local ring, the single weighted ideal has precisely
the same high-order locus as all coefficient conditions together. -/
theorem etale_local_weightedCoefficientIdeal_order_iff
    (x : σ → K) (q : Ideal S) [q.IsMaximal] [q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x)]
    (b : ℕ) (J : Fin b → Ideal (Localization.AtPrime q)) :
    weightedCoefficientIdeal b J ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ b.factorial ↔
      ∀ j, J j ≤ IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (b - j.val) := by
  constructor
  · intro h j
    have hj := (le_iSup (fun j => J j ^ coefficientWeight b j) j).trans h
    rw [← coefficientWeight_mul_control b j] at hj
    exact (Blowups.Etale.PowerOrder.Construction.etale_local_ideal_pow_le_pow_iff x q (J j) (b - j.val)
      (coefficientWeight b j) (coefficientWeight_pos b j)).mp hj
  · exact weightedCoefficientIdeal_le_pow _ b J

/-- Formation of the weighted coefficient ideal commutes with passage to
the local ring, so it defines one ideal on the affine chart. -/
theorem etale_weightedCoefficientIdeal_local_order_iff
    (x : σ → K) (q : Ideal S) [q.IsMaximal] [q.LiesOver (PolynomialTranslation.Construction.polynomialPointIdeal x)]
    (b : ℕ) (J : Fin b → Ideal S) :
    (weightedCoefficientIdeal b J).map (algebraMap S (Localization.AtPrime q)) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ b.factorial ↔
      ∀ j, (J j).map (algebraMap S (Localization.AtPrime q)) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ (b - j.val) := by
  rw [weightedCoefficientIdeal_map]
  exact etale_local_weightedCoefficientIdeal_order_iff x q b _

end

end OAI.AlgebraicGeometry.Resolution.Blowups.WeightedCoefficientIdeal.Construction
