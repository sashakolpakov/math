import Mathlib.Algebra.Ring.Commute
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Hecke Polynomial -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HeckePolynomial.CM

/-!
# Algebraic steps in the manuscript's Hecke calculation

These are proofs of the algebraic deductions in equations (7)--(9).
The actual ordinary-reduction identities and the Satake description must
still be established for the geometric operators. None is asserted here
as a known background result.
-/

/-- The cancellation after equation (8) works in an endomorphism ring.
Only commutation of Frobenius with the two ordinary point operators is
needed; the point operators need not commute with one another. -/
theorem ordinary_hecke_polynomial_cancellation {R : Type*} [Ring R]
    (q : ℕ) (X Y Z : R) (hXY : Commute X Y) (hXZ : Commute X Z) :
    X ^ 3 - (X + q • Y) * X ^ 2 + q • ((X * Y + q ^ 2 • Z) * X) -
      q ^ 3 • (X * Z) = 0 := by
  have hYX : Y * X = X * Y := hXY.eq.symm
  have hZX : Z * X = X * Z := hXZ.eq.symm
  simp only [pow_succ, pow_zero, one_mul, add_mul, smul_mul_assoc, smul_add,
    smul_smul, ← mul_assoc, hYX, hZX]
  abel

/-- Insert the three ordinary-neighbor identities into the cubic. The
hypotheses are data still to be proved on the geometric point operators. -/
theorem ordinary_hecke_polynomial_of_neighbors {R : Type*} [Ring R]
    (q : ℕ) (X Y Z A B C : R) (hXY : Commute X Y) (hXZ : Commute X Z)
    (hA : A = X + q • Y) (hB : B = X * Y + q ^ 2 • Z) (hC : C = X * Z) :
    X ^ 3 - A * X ^ 2 + q • (B * X) - q ^ 3 • C = 0 := by
  rw [hA, hB, hC]
  exact ordinary_hecke_polynomial_cancellation q X Y Z hXY hXZ

/-- Elementary-symmetric coefficients give the three candidate roots.
This purely algebraic identity is the factorization used after Satake. -/
theorem hecke_cubic_factorization {R : Type*} [CommRing R]
    (q b a₁ a₂ a₃ x : R) :
    x ^ 3 - q * b * (a₁ + a₂ + a₃) * x ^ 2 +
      q ^ 2 * b ^ 2 * (a₁ * a₂ + a₁ * a₃ + a₂ * a₃) * x -
      q ^ 3 * b ^ 3 * (a₁ * a₂ * a₃) =
      (x - q * b * a₁) * (x - q * b * a₂) * (x - q * b * a₃) := by
  ring

/-- Weil absolute value selects the middle Satake root. The three-root
assertion is explicit; this theorem does not assert it for any variety. -/
theorem weil_norm_selects_middle_root (q : ℝ) (hq : 1 < q) (b e x : ℂ)
    (hb : ‖b‖ = 1) (he : ‖e‖ = 1) (hx : ‖x‖ = Real.sqrt q)
    (hroot : (x - q * b * (Real.sqrt q : ℂ)) *
      (x - q * b / (Real.sqrt q : ℂ)) * (x - q * b * e) = 0) :
    x = b * (Real.sqrt q : ℂ) := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hs0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hsn : ‖(Real.sqrt q : ℂ)‖ = Real.sqrt q :=
    Complex.norm_of_nonneg hs0.le
  have hqn : ‖(q : ℂ)‖ = q := Complex.norm_of_nonneg hq0.le
  rcases mul_eq_zero.mp hroot with hpair | hlast
  · rcases mul_eq_zero.mp hpair with hfirst | hmiddle
    · have heq := congrArg norm (sub_eq_zero.mp hfirst)
      rw [hx, norm_mul, norm_mul, hqn, hb, hsn, mul_one] at heq
      nlinarith [mul_pos (sub_pos.mpr hq) hs0]
    · have hs : (Real.sqrt q : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
      have hsq : (Real.sqrt q : ℂ) * (Real.sqrt q : ℂ) = (q : ℂ) := by
        exact_mod_cast Real.mul_self_sqrt hq0.le
      rw [sub_eq_zero.mp hmiddle]
      apply (div_eq_iff hs).mpr
      rw [mul_assoc, hsq, mul_comm]
  · have heq := congrArg norm (sub_eq_zero.mp hlast)
    rw [hx, norm_mul, norm_mul, hqn, hb, he, mul_one, mul_one] at heq
    exact (ne_of_lt (Real.sqrt_lt_self_iff.mpr hq) heq).elim

/-- The two possible parameter valuations yield exactly the two Hodge
slopes in equation (9). This is the numerical part, without a comparison
or weak-admissibility assumption hidden in its statement. -/
theorem cm_parameter_slope_dichotomy (v : ℚ) (hv : v = -(3 / 2) ∨ v = 3 / 2) :
    (1 / 2 - v / 3 : ℚ) = 0 ∨ (1 / 2 - v / 3 : ℚ) = 1 := by
  rcases hv with rfl | rfl
  all_goals norm_num

end OAI.AlgebraicGeometry.ComplexMultiplication.HeckePolynomial.CM
