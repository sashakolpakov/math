import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Reflection Congruence Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionCongruenceCoefficients

/-! Explicit denominator cancellation for both orders of a product of
nearby reflections. The relative norm denominator is a unit in every local
ring where the prescribed level belongs to the maximal ideal. These scalar
identities still require instantiation with the actual Hermitian coefficients.
-/

section Ring

variable {R : Type*} [CommRing R]

def reflectionNormDenominator (ℓ q s t r : R) : R :=
  1 + ℓ * q * (s + t) + ℓ ^ 2 * q ^ 3 * r

theorem perturbed_reflection_norm_factor (ℓ q s t r : R) :
    q + (ℓ * q ^ 2) * (s + t) + (ℓ * q ^ 2) ^ 2 * r =
      q * reflectionNormDenominator ℓ q s t r := by
  unfold reflectionNormDenominator
  ring

theorem reflectionNormDenominator_modulo
    {T : Type*} [CommRing T] (f : R →+* T) (ℓ q s t r : R) (hℓ : f ℓ = 0) :
    f (reflectionNormDenominator ℓ q s t r) = 1 := by
  simp [reflectionNormDenominator, hℓ]

theorem reflectionNormDenominator_isUnit [IsLocalRing R]
    (ℓ q s t r : R) (hℓ : ℓ ∈ IsLocalRing.maximalIdeal R) :
    IsUnit (reflectionNormDenominator ℓ q s t r) := by
  apply IsLocalRing.isUnit_of_mem_nonunits_one_sub_self
  have he : 1 - reflectionNormDenominator ℓ q s t r =
      -(q * (s + t) + ℓ * q ^ 3 * r) * ℓ := by
    unfold reflectionNormDenominator
    ring
  rw [he]
  exact (IsLocalRing.maximalIdeal R).mul_mem_left _ hℓ

def forwardReflectionDifferencePolynomial (q m a c p d s t r : R) : R :=
  2 * (q * (c * p - a * d) + (s - t) * a * p +
    m * (-q * c * d - r * a * p + 2 * s * c * p))

def reverseReflectionDifferencePolynomial (q m a c p d s t r : R) : R :=
  2 * (-q * c * p + q * a * d + (t - s) * a * p +
    m * (-q * c * d - r * a * p + 2 * t * a * d))

end Ring

variable {K : Type*} [Field K]

/-- Once the relative norm is a unit in the actual local coefficient ring,
division by it still leaves a literal level multiple from that ring. -/
theorem local_reflection_norm_division_is_level_multiple
    {R : Type*} [CommRing R] [IsLocalRing R] (f : R →+* K)
    (ℓ q s t r P : R) (hℓ : ℓ ∈ IsLocalRing.maximalIdeal R) :
    ∃ a : R, f ℓ * f P / f (reflectionNormDenominator ℓ q s t r) = f (ℓ * a) := by
  have hunit := reflectionNormDenominator_isUnit ℓ q s t r hℓ
  have hnonzero : f (reflectionNormDenominator ℓ q s t r) ≠ 0 := (hunit.map f).ne_zero
  obtain ⟨u, hu⟩ := hunit
  have hinv : f (↑(u⁻¹) : R) * f (reflectionNormDenominator ℓ q s t r) = 1 := by
    rw [← hu, ← map_mul, Units.inv_mul, map_one]
  refine ⟨P * (↑(u⁻¹) : R), (div_eq_iff hnonzero).mpr ?_⟩
  simp only [map_mul, mul_assoc, hinv, mul_one]

/-- The coefficient of `r_(w+m*c) * r_w - 1`, after substituting
`m = level * norm(w)^2`, is a level multiple with only the relative
norm denominator left. -/
theorem forwardReflectionDifference_eq_level_multiple
    (ℓ q a c p d s t r : K) (hq : q ≠ 0)
    (hD : reflectionNormDenominator ℓ q s t r ≠ 0) :
    let m := ℓ * q ^ 2;
    let Q := q + m * (s + t) + m ^ 2 * r;
    -2 * (a + m * c) * (p + m * d) / Q - 2 * a * p / q +
      4 * (a + m * c) * (q + m * s) * p / (Q * q) =
      ℓ * forwardReflectionDifferencePolynomial q m a c p d s t r /
        reflectionNormDenominator ℓ q s t r := by
  dsimp only
  simp only [perturbed_reflection_norm_factor]
  field_simp [hq, hD]
  unfold reflectionNormDenominator forwardReflectionDifferencePolynomial
  ring

/-- The inverse product has the same denominator control. -/
theorem reverseReflectionDifference_eq_level_multiple
    (ℓ q a c p d s t r : K) (hq : q ≠ 0)
    (hD : reflectionNormDenominator ℓ q s t r ≠ 0) :
    let m := ℓ * q ^ 2;
    let Q := q + m * (s + t) + m ^ 2 * r;
    -2 * a * p / q - 2 * (a + m * c) * (p + m * d) / Q +
      4 * a * (q + m * t) * (p + m * d) / (q * Q) =
      ℓ * reverseReflectionDifferencePolynomial q m a c p d s t r /
        reflectionNormDenominator ℓ q s t r := by
  dsimp only
  simp only [perturbed_reflection_norm_factor]
  field_simp [hq, hD]
  unfold reflectionNormDenominator reverseReflectionDifferencePolynomial
  ring

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionCongruenceCoefficients
