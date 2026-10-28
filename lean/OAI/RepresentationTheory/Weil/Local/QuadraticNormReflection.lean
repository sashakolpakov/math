import OAI.RepresentationTheory.Weil.Local.DiagonalAlgebra

/-! # Quadratic Norm Reflection -/

namespace OAI.RepresentationTheory.Weil.Local.QuadraticNormReflection.Construction

noncomputable section

/-! A symmetric change of two coordinates scales x²+y² by a nonzero quadratic norm. -/

open _root_.Matrix

variable {k : Type} [Field k]

def quadraticNormReflection (s t : k) : Matrix (Fin 2) (Fin 2) k := !![s, t; t, -s]

theorem quadraticNormReflection_isSymm (s t : k) : (quadraticNormReflection s t).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem quadraticNormReflection_square (s t : k) :
    quadraticNormReflection s t * quadraticNormReflection s t = (s ^ 2 + t ^ 2) • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [quadraticNormReflection, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

def quadraticNormGeneralLinear (s t : k) (h : s ^ 2 + t ^ 2 ≠ 0) : FunctionsMetaplectic.Construction.GeneralLinear k 2 where
  val := quadraticNormReflection s t
  inv := (s ^ 2 + t ^ 2)⁻¹ • quadraticNormReflection s t
  val_inv := by
    rw [mul_smul_comm, quadraticNormReflection_square, smul_smul, inv_mul_cancel₀ h, one_smul]
  inv_val := by
    rw [smul_mul_assoc, quadraticNormReflection_square, smul_smul, inv_mul_cancel₀ h, one_smul]

theorem quadratic_pair_constant (c : k) (x : FunctionsMetaplectic.Construction.Position k 2) :
    FunctionsMetaplectic.Construction.quadratic (diagonal fun _ : Fin 2 => c) x = c * (x 0 ^ 2 + x 1 ^ 2) / 2 := by
  rw [RealDiagonalFresnel.Construction.quadratic_diagonal]
  simp only [Fin.sum_univ_two]
  ring

theorem quadratic_normReflection (s t c : k) (x : FunctionsMetaplectic.Construction.Position k 2) :
    FunctionsMetaplectic.Construction.quadratic (diagonal fun _ : Fin 2 => c) (quadraticNormReflection s t *ᵥ x) =
      FunctionsMetaplectic.Construction.quadratic (diagonal fun _ : Fin 2 => c * (s ^ 2 + t ^ 2)) x := by
  rw [quadratic_pair_constant, quadratic_pair_constant]
  simp [quadraticNormReflection, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem quadratic_normGeneralLinear_inverse (s t c : k) (h : s ^ 2 + t ^ 2 ≠ 0)
    (x : FunctionsMetaplectic.Construction.Position k 2) :
    FunctionsMetaplectic.Construction.quadratic (diagonal fun _ : Fin 2 => c) ((quadraticNormGeneralLinear s t h)⁻¹.val *ᵥ x) =
      FunctionsMetaplectic.Construction.quadratic (diagonal fun _ : Fin 2 => c / (s ^ 2 + t ^ 2)) x := by
  rw [quadratic_pair_constant, quadratic_pair_constant]
  change c * (((((s ^ 2 + t ^ 2)⁻¹ • quadraticNormReflection s t) *ᵥ x) 0) ^ 2 +
    ((((s ^ 2 + t ^ 2)⁻¹ • quadraticNormReflection s t) *ᵥ x) 1) ^ 2) / 2 = _
  simp [quadraticNormReflection, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  field_simp
  ring

end

end OAI.RepresentationTheory.Weil.Local.QuadraticNormReflection.Construction
