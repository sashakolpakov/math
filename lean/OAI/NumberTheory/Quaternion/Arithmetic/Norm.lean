import OAI.NumberTheory.Quaternion.Arithmetic.CharacterKernelApproximation
import Mathlib.Algebra.Quaternion

/-! # Norm -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.Norm

noncomputable section

/-! The reduced norm and invertibility of a quaternion algebra with
arbitrary nonzero structure constants. No division-algebra assumption
is needed, so the constructions also cover split local factors. -/

open scoped Classical _root_.Quaternion
open QuaternionAlgebra

variable {F : Type*} [Field F] (a b : F)

def quaternionNorm : ℍ[F,a,b] →*₀ F where
  toFun q := (q * star q).re
  map_zero' := by simp only [star_zero, zero_mul, re_zero]
  map_one' := by simp only [star_one, one_mul, re_one]
  map_mul' x y := QuaternionAlgebra.coe_injective <| by
    conv_lhs => rw [← mul_star_eq_coe, star_mul, mul_assoc, ← mul_assoc y, y.mul_star_eq_coe,
      coe_commutes, ← mul_assoc, x.mul_star_eq_coe, ← coe_mul]

theorem quaternionNorm_formula (q : ℍ[F,a,b]) :
    quaternionNorm a b q = q.re ^ 2 - a * q.imI ^ 2 - b * q.imJ ^ 2 + a * b * q.imK ^ 2 := by
  simp only [quaternionNorm, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
    re_mul, re_star, imI_star, imJ_star, imK_star]
  ring

theorem quaternion_mul_star (q : ℍ[F,a,b]) :
    q * star q = (quaternionNorm a b q : ℍ[F,a,b]) := q.mul_star_eq_coe

theorem quaternion_star_mul (q : ℍ[F,a,b]) :
    star q * q = (quaternionNorm a b q : ℍ[F,a,b]) := by
  rw [star_comm_self' q, quaternion_mul_star]

def quaternionUnitOfNormNeZero (q : ℍ[F,a,b]) (hq : quaternionNorm a b q ≠ 0) : ℍ[F,a,b]ˣ where
  val := q
  inv := (quaternionNorm a b q)⁻¹ • star q
  val_inv := by
    rw [Algebra.mul_smul_comm, quaternion_mul_star, smul_coe, inv_mul_cancel₀ hq, coe_one]
  inv_val := by
    rw [Algebra.smul_mul_assoc, quaternion_star_mul, smul_coe, inv_mul_cancel₀ hq, coe_one]

theorem quaternion_isUnit_iff (q : ℍ[F,a,b]) : IsUnit q ↔ quaternionNorm a b q ≠ 0 := by
  constructor
  · intro hq
    exact (hq.map (quaternionNorm a b)).ne_zero
  · intro hq
    exact (quaternionUnitOfNormNeZero a b q hq).isUnit

def quaternionUnitNorm : ℍ[F,a,b]ˣ →* Fˣ := Units.map (quaternionNorm a b).toMonoidHom

@[simp] theorem quaternionUnitNorm_val (q : ℍ[F,a,b]ˣ) :
    (quaternionUnitNorm a b q).val = quaternionNorm a b q.val := rfl

end

end OAI.NumberTheory.Quaternion.Arithmetic.Norm
