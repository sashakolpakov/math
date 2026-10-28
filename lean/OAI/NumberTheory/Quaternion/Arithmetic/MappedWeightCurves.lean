import OAI.NumberTheory.Quaternion.Arithmetic.LocalWeightCurves
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-! # Mapped Weight Curves -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.MappedWeightCurves

noncomputable section

/-! Coefficient maps carry integer-weight curves and their tangent
matrices into the complete local scalar-extension algebra. -/

open scoped Classical _root_.Matrix.Norms.Operator

section

variable {E A : Type*} [Field E] [CommRing A] {n : ℕ}

def integerWeightMatrix (B : Matrix.SpecialLinearGroup (Fin n) E) (m : Fin n → ℤ) :
    Matrix (Fin n) (Fin n) E :=
  (B : Matrix (Fin n) (Fin n) E) * Matrix.diagonal (fun i => (m i : E)) *
    ((B⁻¹ : Matrix.SpecialLinearGroup (Fin n) E) : Matrix (Fin n) (Fin n) E)

theorem map_integerWeightMatrix (f : E →+* A) (B : Matrix.SpecialLinearGroup (Fin n) E)
    (m : Fin n → ℤ) :
    (integerWeightMatrix B m).map f =
      (B : Matrix (Fin n) (Fin n) E).map f * Matrix.diagonal (fun i => (m i : A)) *
        ((B⁻¹ : Matrix.SpecialLinearGroup (Fin n) E) : Matrix (Fin n) (Fin n) E).map f := by
  unfold integerWeightMatrix
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero f)]
  simp only [map_intCast]

theorem unitPower_map_unit (f : E →+* A) (u : Eˣ) (m : ℤ) :
    LocalUnitPowers.unitPower (f u) m = f ((u ^ m : Eˣ) : E) := by
  have h := LocalUnitPowers.unitPower_unit (Units.map f.toMonoidHom u) m
  simpa only [Units.coe_map, ← map_zpow] using! h

end

variable {K E A : Type*} [NontriviallyNormedField K] [Field E] [NormedCommRing A]
  [NormedAlgebra K A] [CompleteSpace K] [CompleteSpace A] [FiniteDimensional K A] {n : ℕ}

def mappedWeightCurve (f : E →+* A) (B : Matrix.SpecialLinearGroup (Fin n) E)
    (a : E) (m : Fin n → ℤ) : K → Matrix (Fin n) (Fin n) A :=
  LocalWeightCurves.localWeightCurve ((B : Matrix (Fin n) (Fin n) E).map f)
    (((B⁻¹ : Matrix.SpecialLinearGroup (Fin n) E) : Matrix (Fin n) (Fin n) E).map f) (f a) m

omit [CompleteSpace K] [CompleteSpace A] [FiniteDimensional K A] in
theorem mappedWeightCurve_zero (f : E →+* A) (B : Matrix.SpecialLinearGroup (Fin n) E)
    (a : E) (m : Fin n → ℤ) : mappedWeightCurve (K := K) f B a m 0 = 1 := by
  rw [mappedWeightCurve, LocalWeightCurves.localWeightCurve_zero, ← Matrix.map_mul]
  rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  exact map_one f.mapMatrix

omit [CompleteSpace K] [CompleteSpace A] [FiniteDimensional K A] in
theorem mappedWeightCurve_at_unit (f : E →+* A) (B : Matrix.SpecialLinearGroup (Fin n) E)
    (a : E) (m : Fin n → ℤ) (t : K) (u : Eˣ) (hu : f u = 1 + t • f a) :
    mappedWeightCurve f B a m t =
      ((B : Matrix (Fin n) (Fin n) E) * Matrix.diagonal (fun i => ((u ^ m i : Eˣ) : E)) *
        ((B⁻¹ : Matrix.SpecialLinearGroup (Fin n) E) : Matrix (Fin n) (Fin n) E)).map f := by
  unfold mappedWeightCurve LocalWeightCurves.localWeightCurve
  rw [← hu, Matrix.map_mul, Matrix.map_mul, Matrix.diagonal_map (map_zero f)]
  simp only [unitPower_map_unit]

theorem mappedWeightCurve_hasDerivAt (f : E →+* A) (B : Matrix.SpecialLinearGroup (Fin n) E)
    (a : E) (m : Fin n → ℤ) :
    HasDerivAt (mappedWeightCurve (K := K) f B a m) ((a • integerWeightMatrix B m).map f) 0 := by
  have hd := LocalWeightCurves.localWeightCurve_hasDerivAt (K := K)
    ((B : Matrix (Fin n) (Fin n) E).map f)
    (((B⁻¹ : Matrix.SpecialLinearGroup (Fin n) E) : Matrix (Fin n) (Fin n) E).map f) (f a) m
  have he : (a • integerWeightMatrix B m).map f = f a • (integerWeightMatrix B m).map f := by
    ext i j
    exact map_mul f a _
  rw [he, map_integerWeightMatrix]
  exact hd

end

end OAI.NumberTheory.Quaternion.Arithmetic.MappedWeightCurves
