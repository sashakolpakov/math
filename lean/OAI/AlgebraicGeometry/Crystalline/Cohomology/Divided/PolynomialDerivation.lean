import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPowers
import Mathlib.RingTheory.Derivation.Basic

/-! # Polynomial Derivation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialDerivation.DividedPolynomialDerivation

noncomputable section

/-!
# Differentiation on the actual divided-polynomial algebra

Transport the integral coefficient shift to the algebra through its
proved divided-monomial basis. Polynomial realization proves the Leibniz
rule. The derivation also respects the constructed relative divided powers.
-/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialAlgebra.DividedPolynomialAlgebra

variable (R : Type*) [CommRing R]
  (K : Type*) [Field K] [CharZero K] [Algebra R K]
  (h : Function.Injective (algebraMap R K))

local notation "G" => DividedPowerAlgebra R R
local notation "e" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialAlgebra.DividedPolynomialAlgebra.coefficientEquiv R K h
local notation "f" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialAlgebra.DividedPolynomialAlgebra.realize R K

def linearDifferential : G →ₗ[R] G :=
  (e).toLinearMap.comp ((Divided.Polynomial.DividedPolynomial.differential R).comp (e).symm.toLinearMap)

theorem linearDifferential_fromCoefficients (a : Divided.Polynomial.DividedPolynomial.Coefficients R) :
    linearDifferential R K h (PolynomialAlgebra.DividedPolynomialAlgebra.fromCoefficients R a) =
      PolynomialAlgebra.DividedPolynomialAlgebra.fromCoefficients R (Divided.Polynomial.DividedPolynomial.differential R a) := by
  change e (Divided.Polynomial.DividedPolynomial.differential R ((e).symm (e a))) = _
  rw [(e).symm_apply_apply]
  rfl

theorem realize_differential (a : G) :
    f (linearDifferential R K h a) = (f a).derivative := by
  obtain ⟨a, rfl⟩ := PolynomialAlgebra.DividedPolynomialAlgebra.fromCoefficients_surjective R a
  rw [linearDifferential_fromCoefficients, PolynomialAlgebra.DividedPolynomialAlgebra.realize_fromCoefficients, PolynomialAlgebra.DividedPolynomialAlgebra.realize_fromCoefficients,
    Divided.Polynomial.DividedPolynomial.derivative_toPolynomial]

/-- The divided-polynomial derivation, with integral coefficient shift. -/
def derivation : Derivation R G G where
  __ := linearDifferential R K h
  map_one_eq_zero' := by
    apply PolynomialAlgebra.DividedPolynomialAlgebra.realize_injective R K h
    change f (linearDifferential R K h 1) = f 0
    rw [realize_differential, map_one, map_zero, Polynomial.derivative_one]
  leibniz' a b := by
    apply PolynomialAlgebra.DividedPolynomialAlgebra.realize_injective R K h
    change f (linearDifferential R K h (a * b)) =
      f (a * linearDifferential R K h b + b * linearDifferential R K h a)
    rw [realize_differential, map_mul, Polynomial.derivative_mul, map_add, map_mul, map_mul,
      realize_differential, realize_differential]
    ring

theorem derivation_monomial_succ (n : ℕ) :
    derivation R K h (PolynomialAlgebra.DividedPolynomialAlgebra.monomial R (n + 1)) = PolynomialAlgebra.DividedPolynomialAlgebra.monomial R n := by
  have hsingle (m : ℕ) : PolynomialAlgebra.DividedPolynomialAlgebra.fromCoefficients R (Finsupp.single m 1) = PolynomialAlgebra.DividedPolynomialAlgebra.monomial R m := by
    rw [PolynomialAlgebra.DividedPolynomialAlgebra.fromCoefficients_single, one_smul]
  rw [← hsingle (n + 1)]
  change linearDifferential R K h (PolynomialAlgebra.DividedPolynomialAlgebra.fromCoefficients R (Finsupp.single (n + 1) 1)) = _
  rw [linearDifferential_fromCoefficients]
  have hd : Divided.Polynomial.DividedPolynomial.differential R (Finsupp.single (n + 1) 1) = Finsupp.single n 1 := by
    ext m
    simp [Divided.Polynomial.DividedPolynomial.differential_apply, Finsupp.single_apply]
  rw [hd, hsingle]

theorem derivation_monomial_zero : derivation R K h (PolynomialAlgebra.DividedPolynomialAlgebra.monomial R 0) = 0 := by
  change derivation R K h (DividedPowerAlgebra.dp R 0 (1 : R)) = 0
  rw [DividedPowerAlgebra.dp_zero, Derivation.map_one_eq_zero]

def primitive : G →ₗ[R] G :=
  (e).toLinearMap.comp ((Divided.Polynomial.DividedPolynomial.primitive R).comp (e).symm.toLinearMap)

theorem derivation_primitive (a : G) : derivation R K h (primitive R K h a) = a := by
  change e (Divided.Polynomial.DividedPolynomial.differential R
    ((e).symm (e (Divided.Polynomial.DividedPolynomial.primitive R ((e).symm a))))) = a
  rw [(e).symm_apply_apply, Divided.Polynomial.DividedPolynomial.differential_primitive, (e).apply_symm_apply]

theorem primitive_derivation (a : G) :
    primitive R K h (derivation R K h a) +
      algebraMap R G ((e).symm a 0) = a := by
  change e (Divided.Polynomial.DividedPolynomial.primitive R
    ((e).symm (e (Divided.Polynomial.DividedPolynomial.differential R ((e).symm a))))) + _ = a
  rw [(e).symm_apply_apply]
  have hc : algebraMap R G ((e).symm a 0) = e (Finsupp.single 0 ((e).symm a 0)) := by
    change _ = PolynomialAlgebra.DividedPolynomialAlgebra.fromCoefficients R (Finsupp.single 0 _)
    rw [PolynomialAlgebra.DividedPolynomialAlgebra.fromCoefficients_single, PolynomialAlgebra.DividedPolynomialAlgebra.monomial, DividedPowerAlgebra.dp_zero, Algebra.smul_def, mul_one]
  rw [hc, ← map_add, Divided.Polynomial.DividedPolynomial.primitive_differential, (e).apply_symm_apply]

theorem derivation_eq_zero_iff (a : G) :
    derivation R K h a = 0 ↔ ∃ c : R, algebraMap R G c = a := by
  constructor
  · intro ha
    refine ⟨(e).symm a 0, ?_⟩
    simpa only [ha, map_zero, zero_add] using primitive_derivation R K h a
  · rintro ⟨c, rfl⟩
    exact (derivation R K h).map_algebraMap c

variable (I : Ideal R) (δ : DividedPowers I) (hunit : ∃ a ∈ I, IsUnit (algebraMap R K a))

local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPowers.DividedPolynomialPowers.ideal R I
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPowers.DividedPolynomialPowers.dividedPowers R K h I δ hunit

/-- The coefficient-shift derivation obeys the PD differential relation. -/
theorem derivation_dpow (n : ℕ) {x : G} (hx : x ∈ J) :
    derivation R K h ((γ).dpow (n + 1) x) = (γ).dpow n x * derivation R K h x := by
  have hd := congrArg (derivation R K h) ((γ).factorial_mul_dpow_eq_pow (n := n + 1) hx)
  rw [(derivation R K h).leibniz, Derivation.map_natCast, smul_zero, add_zero,
    Derivation.leibniz_pow] at hd
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel] at hd
  have heq : ((n + 1).factorial : G) * derivation R K h ((γ).dpow (n + 1) x) =
      ((n + 1).factorial : G) * ((γ).dpow n x * derivation R K h x) := by
    rw [hd, ← (γ).factorial_mul_dpow_eq_pow (n := n) hx, Nat.factorial_succ, Nat.cast_mul]
    ring
  apply PolynomialAlgebra.DividedPolynomialAlgebra.realize_injective R K h
  apply mul_left_cancel₀ (show ((n + 1).factorial : Polynomial K) ≠ 0 from
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  simpa only [map_mul, map_natCast] using congrArg f heq

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialDerivation.DividedPolynomialDerivation
