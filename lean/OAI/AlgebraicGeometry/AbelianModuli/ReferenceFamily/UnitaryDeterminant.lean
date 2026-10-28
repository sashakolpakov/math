import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Groups
import OAI.NumberTheory.CMField.NormOneUnits

/-! # Unitary Determinant -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UnitaryDeterminant

noncomputable section

/-! The determinant of an actual isometry of the reference Hermitian
form has CM norm one. The argument is the determinant of its matrix
isometry equation. -/

open scoped Classical

variable {E : Type*} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem hermitian_basis (b : E) (i j : Fin 3) :
    NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b (Pi.single i 1) (Pi.single j 1) =
      (Matrix.diagonal (fun k : Fin 3 => if k = 2 then b else 1)) i j := by
  by_cases h : i = j
  · subst j
    simp [NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian, Pi.single_apply]
  · simp [NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian, Pi.single_apply, h, Ne.symm h]

theorem unitary_matrix_equation (b : E) (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hg : ∀ x y, NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b (g x) (g y) = NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b x y) :
    (LinearMap.toMatrix' g.toLinearMap).transpose *
        Matrix.diagonal (fun k : Fin 3 => if k = 2 then b else 1) *
          (LinearMap.toMatrix' g.toLinearMap).map (NumberField.IsCMField.complexConj E) =
      Matrix.diagonal (fun k : Fin 3 => if k = 2 then b else 1) := by
  ext i j
  have h := (hg (Pi.single i 1) (Pi.single j 1)).trans (hermitian_basis b i j)
  change (∑ k, (if k = 2 then b else 1) * g (Pi.single i 1) k *
      NumberField.IsCMField.complexConj E (g (Pi.single j 1) k)) = _ at h
  change (∑ k, ((LinearMap.toMatrix' g.toLinearMap).transpose *
    Matrix.diagonal (fun k : Fin 3 => if k = 2 then b else 1)) i k *
      ((LinearMap.toMatrix' g.toLinearMap).map (NumberField.IsCMField.complexConj E)) k j) = _
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply,
    Matrix.map_apply, LinearMap.toMatrix'_apply]
  calc
    _ = ∑ k, (if k = 2 then b else 1) * g (Pi.single i 1) k *
        NumberField.IsCMField.complexConj E (g (Pi.single j 1) k) := by
      apply Finset.sum_congr rfl
      intro k _
      change (g (Pi.single i 1) k * (if k = 2 then b else 1)) * _ = _
      rw [mul_comm (g (Pi.single i 1) k)]
      rfl
    _ = _ := h

theorem unitary_det_norm_one (b : E) (hb : b ≠ 0)
    (g : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E ≃ₗ[E] NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E)
    (hg : ∀ x y, NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b (g x) (g y) = NumberTheory.ArithmeticGroups.Data.CongruenceLevel.hermitian b x y) :
    LinearMap.det g.toLinearMap *
      NumberField.IsCMField.complexConj E (LinearMap.det g.toLinearMap) = 1 := by
  have h := congrArg Matrix.det (unitary_matrix_equation b g hg)
  have hmap : ((LinearMap.toMatrix' g.toLinearMap).map
      (NumberField.IsCMField.complexConj E)).det =
        NumberField.IsCMField.complexConj E (LinearMap.toMatrix' g.toLinearMap).det :=
    ((NumberField.IsCMField.complexConj E).map_det _).symm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hmap, Matrix.det_diagonal] at h
  have hd : (∏ i : Fin 3, if i = 2 then b else 1) = b := by simp
  rw [hd, LinearMap.det_toMatrix'] at h
  apply (mul_right_cancel₀ hb)
  calc
    (LinearMap.det g.toLinearMap *
        NumberField.IsCMField.complexConj E (LinearMap.det g.toLinearMap)) * b =
      LinearMap.det g.toLinearMap * b *
        NumberField.IsCMField.complexConj E (LinearMap.det g.toLinearMap) := by ring
    _ = b := h
    _ = 1 * b := (one_mul b).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UnitaryDeterminant
