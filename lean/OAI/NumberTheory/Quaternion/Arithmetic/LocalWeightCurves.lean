import OAI.NumberTheory.Quaternion.Arithmetic.LocalUnitPowers
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Local Weight Curves -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.LocalWeightCurves

noncomputable section

/-! Local integer-weight curves in a finite-dimensional complete
commutative algebra, with their concrete matrix derivative at the identity. -/

open scoped Classical _root_.Matrix.Norms.Operator

variable {K A : Type*} [NontriviallyNormedField K] [NormedCommRing A]
  [NormedAlgebra K A] [CompleteSpace K] [CompleteSpace A] [FiniteDimensional K A] {n : ℕ}

def localWeightCurve (B C : Matrix (Fin n) (Fin n) A) (a : A) (m : Fin n → ℤ) (t : K) :
    Matrix (Fin n) (Fin n) A :=
  B * Matrix.diagonal (fun i => LocalUnitPowers.unitPower (1 + t • a) (m i)) * C

omit [CompleteSpace K] [CompleteSpace A] [FiniteDimensional K A] in
theorem localWeightCurve_zero (B C : Matrix (Fin n) (Fin n) A) (a : A) (m : Fin n → ℤ) :
    localWeightCurve (K := K) B C a m 0 = B * C := by
  simp only [localWeightCurve, zero_smul, add_zero, LocalUnitPowers.unitPower_one, Matrix.diagonal_one, mul_one]

theorem diagonalWeightCurve_hasDerivAt (a : A) (m : Fin n → ℤ) :
    HasDerivAt (fun t : K => Matrix.diagonal (fun i => LocalUnitPowers.unitPower (1 + t • a) (m i)))
      (Matrix.diagonal (fun i => (m i : K) • a)) 0 := by
  let d : (Fin n → A) →L[K] Matrix (Fin n) (Fin n) A :=
    (Matrix.diagonalLinearMap (Fin n) K A).toContinuousLinearMap
  have h : HasDerivAt (fun t : K => fun i : Fin n => LocalUnitPowers.unitPower (1 + t • a) (m i))
      (fun i => (m i : K) • a) 0 := hasDerivAt_pi.mpr (fun i => LocalUnitPowers.unitPower_affine_hasDerivAt a (m i))
  simpa only [d, Function.comp_def, LinearMap.coe_toContinuousLinearMap,
    Matrix.diagonalLinearMap_apply] using! d.hasFDerivAt.comp_hasDerivAt 0 h

omit [CompleteSpace K] [CompleteSpace A] [FiniteDimensional K A] in
theorem diagonalWeight_scalar (a : A) (m : Fin n → ℤ) :
    Matrix.diagonal (fun i => (m i : K) • a) = a • Matrix.diagonal (fun i => (m i : A)) := by
  rw [← Matrix.diagonal_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Int.cast_smul_eq_zsmul, zsmul_eq_mul, mul_comm]

theorem localWeightCurve_hasDerivAt (B C : Matrix (Fin n) (Fin n) A) (a : A) (m : Fin n → ℤ) :
    HasDerivAt (localWeightCurve (K := K) B C a m)
      (a • (B * Matrix.diagonal (fun i => (m i : A)) * C)) 0 := by
  have h := ((diagonalWeightCurve_hasDerivAt (K := K) a m).const_mul B).mul_const C
  simpa only [localWeightCurve, diagonalWeight_scalar, Matrix.mul_smul, Matrix.smul_mul] using! h

end

end OAI.NumberTheory.Quaternion.Arithmetic.LocalWeightCurves
