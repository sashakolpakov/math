import OAI.AlgebraicGeometry.HilbertScheme.Presentations.PrimeLocalizationUnitUniqueness

/-! # Prime Localization Unit Exponent -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.PrimeLocalizationUnitExponent

noncomputable section

/-! The prime-coordinate exponent is a canonical integer invariant
of localization units and is additive under multiplication. -/

universe u v
variable {R : Type u} [CommRing R] [IsDomain R]
variable {A : Type v} [CommRing A] [Algebra R A]

structure PrimeLocalizationUnitData (p : R) (z : Aˣ) where
  scalar : Rˣ
  numerator : ℕ
  denominator : ℕ
  equation : (z : A) * algebraMap R A p ^ denominator =
    algebraMap R A (scalar : R) * algebraMap R A p ^ numerator

variable (p : R) (hp : Prime p) [IsLocalization.Away p A]

def primeLocalizationUnitData (z : Aˣ) : PrimeLocalizationUnitData p z := by
  apply Classical.choice
  obtain ⟨c, a, b, h⟩ := PrimeLocalizationUnits.primeLocalization_unit_powers p hp z
  exact ⟨⟨c, a, b, h⟩⟩

def primeLocalizationUnitExponent (z : Aˣ) : ℤ :=
  ((primeLocalizationUnitData p hp z).numerator : ℤ) - (primeLocalizationUnitData p hp z).denominator

theorem primeLocalizationUnitExponent_of_equation (z : Aˣ) (c : Rˣ) (a b : ℕ)
    (h : (z : A) * algebraMap R A p ^ b = algebraMap R A (c : R) * algebraMap R A p ^ a) :
    primeLocalizationUnitExponent p hp z = (a : ℤ) - b :=
  (PrimeLocalizationUnitUniqueness.primeLocalization_unit_exponent_unique p hp z (primeLocalizationUnitData p hp z).scalar c
    (primeLocalizationUnitData p hp z).numerator (primeLocalizationUnitData p hp z).denominator a b
    (primeLocalizationUnitData p hp z).equation h).2

theorem primeLocalizationUnitExponent_mul (z w : Aˣ) :
    primeLocalizationUnitExponent p hp (z * w) =
      primeLocalizationUnitExponent p hp z + primeLocalizationUnitExponent p hp w := by
  let D := primeLocalizationUnitData p hp z
  let E := primeLocalizationUnitData p hp w
  have h : ((z * w : Aˣ) : A) * algebraMap R A p ^ (D.denominator + E.denominator) =
      algebraMap R A ((D.scalar * E.scalar : Rˣ) : R) *
        algebraMap R A p ^ (D.numerator + E.numerator) := by
    simp only [Units.val_mul, map_mul, pow_add]
    calc
      _ = ((z : A) * algebraMap R A p ^ D.denominator) *
          ((w : A) * algebraMap R A p ^ E.denominator) := by ring
      _ = (algebraMap R A (D.scalar : R) * algebraMap R A p ^ D.numerator) *
          (algebraMap R A (E.scalar : R) * algebraMap R A p ^ E.numerator) :=
        congrArg₂ (fun a b : A => a * b) D.equation E.equation
      _ = _ := by ring
  rw [primeLocalizationUnitExponent_of_equation p hp (z * w) (D.scalar * E.scalar)
    (D.numerator + E.numerator) (D.denominator + E.denominator) h]
  change ((D.numerator + E.numerator : ℕ) : ℤ) - (D.denominator + E.denominator : ℕ) =
    ((D.numerator : ℤ) - D.denominator) + ((E.numerator : ℤ) - E.denominator)
  omega

theorem primeLocalizationUnitExponent_one : primeLocalizationUnitExponent (A := A) p hp 1 = 0 := by
  have h : ((1 : Aˣ) : A) * algebraMap R A p ^ 0 =
      algebraMap R A ((1 : Rˣ) : R) * algebraMap R A p ^ 0 := by simp
  simpa only [Int.natCast_zero, sub_zero] using primeLocalizationUnitExponent_of_equation p hp 1 1 0 0 h

theorem primeLocalizationUnitExponent_inv (z : Aˣ) :
    primeLocalizationUnitExponent p hp z⁻¹ = -primeLocalizationUnitExponent p hp z := by
  have h := primeLocalizationUnitExponent_mul p hp z z⁻¹
  rw [mul_inv_cancel, primeLocalizationUnitExponent_one] at h
  omega

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.PrimeLocalizationUnitExponent
