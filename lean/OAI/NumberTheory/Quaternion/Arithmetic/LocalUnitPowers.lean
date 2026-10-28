import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Local Unit Powers -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.LocalUnitPowers

noncomputable section

/-! Integer powers on the unit neighborhood of a complete commutative
normed algebra, including their derivative along an affine parameter. -/

open scoped Classical
open _root_.ContinuousLinearMap

section

variable {A : Type*} [CommRing A]

def unitPower (x : A) : ℤ → A
  | .ofNat n => x ^ n
  | .negSucc n => (Ring.inverse x) ^ (n + 1)

theorem unitPower_unit (u : Aˣ) (m : ℤ) : unitPower (u : A) m = ((u ^ m : Aˣ) : A) := by
  cases m with
  | ofNat n => simp [unitPower]
  | negSucc n => simp [unitPower, zpow_negSucc]

theorem unitPower_one (m : ℤ) : unitPower (1 : A) m = 1 := by
  cases m <;> simp [unitPower, Ring.inverse_one]

end

variable {K A : Type*} [NontriviallyNormedField K] [NormedCommRing A]
  [NormedAlgebra K A] [CompleteSpace A]

omit [CompleteSpace A] in
theorem affineUnit_hasDerivAt (a : A) :
    HasDerivAt (fun t : K => 1 + t • a) a 0 := by
  simpa only [one_smul, id_eq] using! ((hasDerivAt_id (0 : K)).smul_const a).const_add 1

theorem inverseAffineUnit_hasDerivAt (a : A) :
    HasDerivAt (fun t : K => Ring.inverse (1 + t • a)) (-a) 0 := by
  have hi : HasFDerivAt Ring.inverse (-mulLeftRight K A (1 : A) 1)
      ((fun t : K => 1 + t • a) 0) := by
    simpa using hasFDerivAt_ringInverse (𝕜 := K) (1 : Aˣ)
  simpa only [Function.comp_def, neg_apply, mulLeftRight_apply, one_mul, mul_one] using!
    hi.comp_hasDerivAt 0 (affineUnit_hasDerivAt (K := K) a)

theorem unitPower_affine_hasDerivAt (a : A) (m : ℤ) :
    HasDerivAt (fun t : K => unitPower (1 + t • a) m) ((m : K) • a) 0 := by
  cases m with
  | ofNat n =>
    simpa only [unitPower, Int.ofNat_eq_natCast, Int.cast_natCast, zero_smul, add_zero, one_pow, mul_one,
      Nat.cast_smul_eq_nsmul, nsmul_eq_mul] using! (affineUnit_hasDerivAt (K := K) a).fun_pow n
  | negSucc n =>
    simp only [unitPower, Int.cast_negSucc]
    simpa only [zero_smul, add_zero, Ring.inverse_one, one_pow, mul_one,
      Nat.cast_smul_eq_nsmul, nsmul_eq_mul, neg_smul, mul_neg] using!
      (inverseAffineUnit_hasDerivAt (K := K) a).fun_pow (n + 1)

end

end OAI.NumberTheory.Quaternion.Arithmetic.LocalUnitPowers
