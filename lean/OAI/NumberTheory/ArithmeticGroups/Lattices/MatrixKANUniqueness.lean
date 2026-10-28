import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.TriangularMatrices

/-! # Matrix KAN Uniqueness -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! Uniqueness of the orthogonal, positive diagonal, upper unitriangular
factorization, with the factors viewed as real matrices. -/

open scoped Classical

theorem Positive.TriangularMatrices.Construction.IsPositiveUpperTriangular.isUnit {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : Positive.TriangularMatrices.Construction.IsPositiveUpperTriangular M) : IsUnit M := by
  apply M.isUnit_iff_isUnit_det.mpr
  apply isUnit_iff_ne_zero.mpr
  rw [Matrix.det_of_isUpperTriangular hM.1]
  exact ne_of_gt (Finset.prod_pos (fun i _ => hM.2 i))

theorem MatrixKANUniqueness.Construction.orthogonal_matrix_unit_inv {n : ℕ} (k : (Matrix (Fin n) (Fin n) ℝ)ˣ)
    (hk : k.val ∈ Matrix.orthogonalGroup (Fin n) ℝ) :
    (k⁻¹).val ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
  have hi : (k⁻¹).val = k.val.transpose :=
    k.inv_eq_of_mul_eq_one_right ((Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp hk)
  apply (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mpr
  rw [hi, Matrix.transpose_transpose]
  exact (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp hk

theorem MatrixKANUniqueness.Construction.orthogonal_positive_triangular_factorization_unique {n : ℕ}
    (k₁ k₂ t₁ t₂ : (Matrix (Fin n) (Fin n) ℝ)ˣ)
    (hk₁ : k₁.val ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (hk₂ : k₂.val ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (ht₁ : Positive.TriangularMatrices.Construction.IsPositiveUpperTriangular t₁.val) (ht₂ : Positive.TriangularMatrices.Construction.IsPositiveUpperTriangular t₂.val)
    (h : k₁ * t₁ = k₂ * t₂) : k₁ = k₂ ∧ t₁ = t₂ := by
  have he : k₂⁻¹ * k₁ = t₂ * t₁⁻¹ := by
    calc
      k₂⁻¹ * k₁ = k₂⁻¹ * (k₁ * t₁) * t₁⁻¹ := by group
      _ = k₂⁻¹ * (k₂ * t₂) * t₁⁻¹ := by rw [h]
      _ = t₂ * t₁⁻¹ := by group
  have hu : Positive.TriangularMatrices.Construction.IsPositiveUpperTriangular (k₂⁻¹ * k₁).val := by
    rw [he]
    exact ht₂.mul (ht₁.unit_inv t₁)
  have ho : (k₂⁻¹ * k₁).val ∈ Matrix.orthogonalGroup (Fin n) ℝ :=
    (Matrix.orthogonalGroup (Fin n) ℝ).mul_mem (MatrixKANUniqueness.Construction.orthogonal_matrix_unit_inv k₂ hk₂) hk₁
  have hk : k₁ = k₂ :=
    (eq_of_inv_mul_eq_one (Positive.TriangularMatrices.Construction.positive_upper_triangular_orthogonal_eq_one _ hu ho)).symm
  refine ⟨hk, ?_⟩
  rw [hk] at h
  exact mul_left_cancel h

theorem MatrixKANUniqueness.Construction.positive_diagonal_mul_unitriangular {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (U : Matrix (Fin n) (Fin n) ℝ) (hU : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular U) :
    Positive.TriangularMatrices.Construction.IsPositiveUpperTriangular (Matrix.diagonal a * U) := by
  have hd : (Matrix.diagonal a).IsUpperTriangular := Matrix.blockTriangular_diagonal a
  refine ⟨hd.mul hU.1, fun i => ?_⟩
  rw [Matrix.diagonal_mul, hU.2 i, mul_one]
  exact ha i

theorem MatrixKANUniqueness.Construction.matrix_kan_factorization_unique {n : ℕ}
    (K₁ K₂ U₁ U₂ : Matrix (Fin n) (Fin n) ℝ) (a₁ a₂ : Fin n → ℝ)
    (hK₁ : K₁ ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (hK₂ : K₂ ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (ha₁ : ∀ i, 0 < a₁ i) (ha₂ : ∀ i, 0 < a₂ i)
    (hU₁ : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular U₁) (hU₂ : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular U₂)
    (h : K₁ * Matrix.diagonal a₁ * U₁ = K₂ * Matrix.diagonal a₂ * U₂) :
    K₁ = K₂ ∧ a₁ = a₂ ∧ U₁ = U₂ := by
  let k₁ := OrthogonalOperatorMatrices.Construction.orthogonalMatrixUnit K₁ hK₁
  let k₂ := OrthogonalOperatorMatrices.Construction.orthogonalMatrixUnit K₂ hK₂
  have hp₁ := MatrixKANUniqueness.Construction.positive_diagonal_mul_unitriangular a₁ ha₁ U₁ hU₁
  have hp₂ := MatrixKANUniqueness.Construction.positive_diagonal_mul_unitriangular a₂ ha₂ U₂ hU₂
  let t₁ := hp₁.isUnit.unit
  let t₂ := hp₂.isUnit.unit
  have ht₁ : t₁.val = Matrix.diagonal a₁ * U₁ := hp₁.isUnit.unit_spec
  have ht₂ : t₂.val = Matrix.diagonal a₂ * U₂ := hp₂.isUnit.unit_spec
  have he : k₁ * t₁ = k₂ * t₂ := by
    apply Units.ext
    change K₁ * t₁.val = K₂ * t₂.val
    rw [ht₁, ht₂, ← mul_assoc, ← mul_assoc]
    exact h
  obtain ⟨hk, ht⟩ := MatrixKANUniqueness.Construction.orthogonal_positive_triangular_factorization_unique
    k₁ k₂ t₁ t₂ hK₁ hK₂ (ht₁.symm ▸ hp₁) (ht₂.symm ▸ hp₂) he
  have he' : Matrix.diagonal a₁ * U₁ = Matrix.diagonal a₂ * U₂ := by
    rw [← ht₁, ← ht₂, ht]
  have ha : a₁ = a₂ := by
    funext i
    have hi := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i i) he'
    simpa only [Matrix.diagonal_mul, hU₁.2 i, hU₂.2 i, mul_one] using hi
  refine ⟨congrArg Units.val hk, ha, ?_⟩
  ext i j
  have hi := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) he'
  rw [← ha, Matrix.diagonal_mul, Matrix.diagonal_mul] at hi
  exact mul_left_cancel₀ (ne_of_gt (ha₁ i)) hi

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
