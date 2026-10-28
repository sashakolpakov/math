import OAI.RepresentationTheory.Weil.AdelicSplitting.PhaseFourier

/-! # Quadratic Matrix Coordinates -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticMatrixCoordinates.Construction

noncomputable section

/-! Symmetric quadratic matrices and change of finite coordinate indices. -/

open scoped Classical _root_.Matrix

variable {F : Type} [Field F] [CharZero F] {N : ℕ}

def symmetricPart (M : Matrix (Fin N) (Fin N) F) : Local.FunctionsMetaplectic.Construction.SymmetricMatrix F N :=
  ⟨(2 : F)⁻¹ • (M + Mᵀ), by
    ext i j
    change (2 : F)⁻¹ * (M j i + M i j) = (2 : F)⁻¹ * (M i j + M j i)
    rw [add_comm]⟩

omit [CharZero F] in
theorem quadratic_eq_toBilin (M : Matrix (Fin N) (Fin N) F) (x : Local.FunctionsMetaplectic.Construction.Position F N) :
    Local.FunctionsMetaplectic.Construction.quadratic M x = M.toBilin' x x / 2 := by rw [Local.FunctionsMetaplectic.Construction.quadratic, Matrix.toBilin'_apply]

omit [CharZero F] in
theorem toBilin_transpose_self {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι F) (x : ι → F) : Mᵀ.toBilin' x x = M.toBilin' x x := by
  simp only [Matrix.toBilin'_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem quadratic_symmetricPart (M : Matrix (Fin N) (Fin N) F) (x : Local.FunctionsMetaplectic.Construction.Position F N) :
    Local.FunctionsMetaplectic.Construction.quadratic (symmetricPart M).val x = M.toBilin' x x / 2 := by
  rw [quadratic_eq_toBilin]
  change (((2 : F)⁻¹ • (M + Mᵀ)).toBilin') x x / 2 = _
  rw [map_smul, map_add]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul, toBilin_transpose_self]
  field_simp
  ring

omit [CharZero F] in
theorem reindex_toBilin {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (e : ι ≃ κ) (M : Matrix ι ι F) (x y : κ → F) :
    (Matrix.reindex e e M).toBilin' x y = M.toBilin' (fun i => x (e i)) (fun i => y (e i)) := by
  simp only [Matrix.toBilin'_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [← e.sum_comp (fun i => ∑ j, x i * M (e.symm i) (e.symm j) * y j)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← e.sum_comp (fun j => x (e i) * M (e.symm (e i)) (e.symm j) * y j)]
  simp only [e.symm_apply_apply]

omit [CharZero F] in
theorem toBilin_transpose_mul_left {ι : Type} [Fintype ι] [DecidableEq ι]
    (M P : Matrix ι ι F) (x y : ι → F) :
    (Pᵀ * M).toBilin' x y = M.toBilin' (P *ᵥ x) y := by
  have hh := congrArg (fun B : LinearMap.BilinForm F (ι → F) => B x y) (Matrix.toBilin'_comp M P 1)
  simpa only [Matrix.mul_one, LinearMap.BilinForm.comp_apply, Matrix.toLin'_apply, Matrix.one_mulVec] using hh.symm

theorem symmetricPart_map {k : Type} [Field k] [CharZero k] (e : F →+* k)
    (M : Matrix (Fin N) (Fin N) F) :
    (symmetricPart M).val.map e = (symmetricPart (M.map e)).val := by
  ext i j
  change e ((2 : F)⁻¹ * (M i j + M j i)) = (2 : k)⁻¹ * (e (M i j) + e (M j i))
  simp only [map_mul, map_inv₀, map_ofNat, map_add]

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.QuadraticMatrixCoordinates.Construction
