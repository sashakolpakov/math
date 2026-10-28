import OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicBoundaryReindex
import OAI.AlgebraicGeometry.Resolution.Blowups.DerivativeHypersurfacePersistence

/-! # Logarithmic Coordinate Power -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicCoordinatePower.Construction

noncomputable section

/-! A coordinate power supplies an explicit logarithmic differential unit-ideal bound. -/

variable {R ι : Type*} [CommRing R]

theorem iteratedRingDerivation_nsmul (D : Derivation ℤ R R) (j n : ℕ) (p : R) :
    D^[j] (n • p) = n • D^[j] p := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', ih, map_nsmul]

/-- The `m`th derivative of the `m`th power of a coordinate is `m!`. -/
theorem iteratedRingDerivation_coordinate_power (D : Derivation ℤ R R) (z : R)
    (hz : D z = 1) (m : ℕ) : D^[m] (z ^ m) = (m.factorial : R) := by
  induction m with
  | zero => simp only [pow_zero, Function.iterate_zero, id_eq, Nat.factorial_zero, Nat.cast_one]
  | succ m ih =>
    rw [Function.iterate_succ_apply, DifferentialBlowupTransform.Construction.ringDerivation_pow_succ D z m, hz, mul_one,
      ← nsmul_eq_mul, iteratedRingDerivation_nsmul, ih]
    simp only [nsmul_eq_mul, Nat.factorial_succ, Nat.cast_mul]

/-- Iterates of any one logarithmic derivation belong to the corresponding
iterated logarithmic differential ideal. -/
theorem iterated_logarithmic_derivation_mem (w : ι → R) (D : LogarithmicDerivation.Construction.logarithmicDerivations w)
    (J : Ideal R) (p : R) (hp : p ∈ J) (n : ℕ) :
    D.val^[n] p ∈ LogarithmicBoundaryReindex.Construction.iteratedLogarithmicDifferentialIdeal w J n := by
  induction n generalizing J p with
  | zero => exact hp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih (LogarithmicBoundaryReindex.Construction.firstLogarithmicDifferentialIdeal w J) (D.val p)
      (LogarithmicBoundaryReindex.Construction.logarithmic_derivation_mem_first w J D hp)

/-- An included coordinate power and a logarithmic derivative taking that
coordinate to one prove the required unit-ideal bound explicitly. -/
theorem logarithmic_bound_of_coordinate_power [Algebra ℚ R]
    (w : ι → R) (D : LogarithmicDerivation.Construction.logarithmicDerivations w) (z : R) (hz : D.val z = 1)
    (J : Ideal R) (m : ℕ) (hzm : z ^ m ∈ J) :
    LogarithmicBoundaryReindex.Construction.iteratedLogarithmicDifferentialIdeal w J m = ⊤ := by
  have hfact := iterated_logarithmic_derivation_mem w D J (z ^ m) hzm m
  rw [iteratedRingDerivation_coordinate_power D.val z hz m] at hfact
  exact Ideal.eq_top_of_isUnit_mem _ hfact (DerivativeHypersurfacePersistence.Construction.factorial_isUnit_of_rationalAlgebra m)

/-- The penultimate derivative of a coordinate power is a unit factorial
multiple of that coordinate in a rational algebra. -/
theorem iteratedRingDerivation_penultimate_power (D : Derivation ℤ R R) (z : R)
    (hz : D z = 1) (m : ℕ) : D^[m] (z ^ (m + 1)) = ((m + 1).factorial : R) * z := by
  induction m with
  | zero => simp only [zero_add, pow_one, Function.iterate_zero, id_eq,
      Nat.factorial_one, Nat.cast_one, one_mul]
  | succ m ih =>
    rw [Function.iterate_succ_apply, DifferentialBlowupTransform.Construction.ringDerivation_pow_succ D z (m + 1), hz, mul_one,
      ← nsmul_eq_mul, iteratedRingDerivation_nsmul, ih]
    simp only [nsmul_eq_mul, Nat.factorial_succ, Nat.cast_mul, mul_assoc]

/-- An included coordinate power supplies that coordinate itself in the
penultimate logarithmic differential ideal, giving a persistent hypersurface equation. -/
theorem coordinate_mem_logarithmic_of_power [Algebra ℚ R]
    (w : ι → R) (D : LogarithmicDerivation.Construction.logarithmicDerivations w) (z : R) (hz : D.val z = 1)
    (J : Ideal R) (m : ℕ) (hzm : z ^ (m + 1) ∈ J) :
    z ∈ LogarithmicBoundaryReindex.Construction.iteratedLogarithmicDifferentialIdeal w J m := by
  have hfact := iterated_logarithmic_derivation_mem w D J (z ^ (m + 1)) hzm m
  rw [iteratedRingDerivation_penultimate_power D.val z hz m] at hfact
  exact (Ideal.unit_mul_mem_iff_mem _ (DerivativeHypersurfacePersistence.Construction.factorial_isUnit_of_rationalAlgebra (m + 1))).mp hfact

end

end OAI.AlgebraicGeometry.Resolution.Blowups.LogarithmicCoordinatePower.Construction
