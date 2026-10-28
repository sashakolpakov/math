import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionCongruenceCoefficients
import Mathlib.Algebra.Ring.GeomSum

/-! # Cleared Reflection Polynomials -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ClearedReflectionPolynomials

/-! Both reflection difference numerators and the relative Hermitian
norm have coefficient degree at most two in the perturbation vector.
One square of its common denominator therefore clears all three.
-/

variable {R : Type*} [CommRing R]

def clearedReflectionNormDenominator (ℓ b q s t r : R) : R :=
  b ^ 2 + ℓ * q * b * (s + t) + ℓ ^ 2 * q ^ 3 * r

def clearedForwardReflectionPolynomial (b q m a c p d s t r : R) : R :=
  2 * (q * b * (c * p - a * d) + b * (s - t) * a * p +
    m * (-q * c * d - r * a * p + 2 * s * c * p))

def clearedReverseReflectionPolynomial (b q m a c p d s t r : R) : R :=
  2 * (b * (-q * c * p + q * a * d) + b * (t - s) * a * p +
    m * (-q * c * d - r * a * p + 2 * t * a * d))

theorem reflectionNormDenominator_clear (ℓ b q s t r : R) :
    b ^ 2 * ReflectionCongruenceCoefficients.reflectionNormDenominator ℓ q s t r =
      clearedReflectionNormDenominator ℓ b q (b * s) (b * t) (b ^ 2 * r) := by
  unfold ReflectionCongruenceCoefficients.reflectionNormDenominator clearedReflectionNormDenominator
  ring

theorem forwardReflectionPolynomial_clear (b q m a c p d s t r : R) :
    b ^ 2 * ReflectionCongruenceCoefficients.forwardReflectionDifferencePolynomial q m a c p d s t r =
      clearedForwardReflectionPolynomial b q m a (b * c) p (b * d)
        (b * s) (b * t) (b ^ 2 * r) := by
  unfold ReflectionCongruenceCoefficients.forwardReflectionDifferencePolynomial clearedForwardReflectionPolynomial
  ring

theorem reverseReflectionPolynomial_clear (b q m a c p d s t r : R) :
    b ^ 2 * ReflectionCongruenceCoefficients.reverseReflectionDifferencePolynomial q m a c p d s t r =
      clearedReverseReflectionPolynomial b q m a (b * c) p (b * d)
        (b * s) (b * t) (b ^ 2 * r) := by
  unfold ReflectionCongruenceCoefficients.reverseReflectionDifferencePolynomial clearedReverseReflectionPolynomial
  ring

theorem clearedReflectionNormDenominator_eq_one_add_level
    (ℓ q s t r : R) (n : ℕ) :
    ∃ u : R, clearedReflectionNormDenominator ℓ ((ℓ + 1) ^ n) q s t r = 1 + ℓ * u := by
  have hd : ℓ ∣ (ℓ + 1) ^ (n * 2) - 1 := by
    simpa only [add_sub_cancel_right, one_pow] using
      (sub_dvd_pow_sub_pow (ℓ + 1) (1 : R) (n * 2))
  obtain ⟨a, ha⟩ := hd
  refine ⟨a + q * (ℓ + 1) ^ n * (s + t) + ℓ * q ^ 3 * r, ?_⟩
  calc
    clearedReflectionNormDenominator ℓ ((ℓ + 1) ^ n) q s t r =
        ((ℓ + 1) ^ (n * 2) - 1) + 1 +
          ℓ * q * (ℓ + 1) ^ n * (s + t) + ℓ ^ 2 * q ^ 3 * r := by
      rw [pow_mul]
      unfold clearedReflectionNormDenominator
      ring
    _ = _ := by rw [ha]; ring

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ClearedReflectionPolynomials
