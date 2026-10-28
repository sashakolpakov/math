import OAI.NumberTheory.ArithmeticGroups.Lattices.UpperUnitriangularMatrices
import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ExponentialMatrixChamber

/-! # Upper Pivot Elimination -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.UpperPivotElimination.Construction

noncomputable section

/-! Upper unitriangular row and column operations isolate the first
nonzero entry of the last row of an invertible matrix. -/

open scoped Classical

def upperColumnShear {n : ℕ} (c : Fin (n + 1) → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  1 + Matrix.vecMulVec c (Pi.single (Fin.last n) 1)

def upperRowShear {n : ℕ} (p : Fin n) (c : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 + Matrix.vecMulVec (Pi.single p 1) c

theorem upperColumnShear_unitriangular {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : c (Fin.last n) = 0) : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (upperColumnShear c) := by
  constructor
  · intro i j hij
    change j < i at hij
    have hj : j ≠ Fin.last n := ne_of_lt (hij.trans_le (Fin.le_last i))
    simp [upperColumnShear, Matrix.vecMulVec_apply, ne_of_gt hij, hj]
  · intro i
    by_cases hi : i = Fin.last n
    · subst i
      simp [upperColumnShear, Matrix.vecMulVec_apply, hc]
    · simp [upperColumnShear, Matrix.vecMulVec_apply, hi]

theorem upperRowShear_unitriangular {n : ℕ} (p : Fin n) (c : Fin n → ℝ)
    (hc : ∀ j, j ≤ p → c j = 0) : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (upperRowShear p c) := by
  constructor
  · intro i j hij
    change j < i at hij
    by_cases hi : i = p
    · subst i
      simp [upperRowShear, Matrix.vecMulVec_apply, ne_of_gt hij, hc j hij.le]
    · simp [upperRowShear, Matrix.vecMulVec_apply, ne_of_gt hij, hi]
  · intro i
    by_cases hi : i = p
    · subst i
      simp [upperRowShear, Matrix.vecMulVec_apply, hc p le_rfl]
    · simp [upperRowShear, Matrix.vecMulVec_apply, hi]

theorem upperColumnShear_mul {n : ℕ} (c : Fin (n + 1) → ℝ)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i j : Fin (n + 1)) :
    (upperColumnShear c * M) i j = M i j + c i * M (Fin.last n) j := by
  simp [upperColumnShear, add_mul, Matrix.vecMulVec_mul,
    Matrix.vecMulVec_apply]

theorem mul_upperRowShear {n : ℕ} (p : Fin n) (c : Fin n → ℝ)
    (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (M * upperRowShear p c) i j = M i j + M i p * c j := by
  simp [upperRowShear, mul_add, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_apply]

theorem exists_upper_pivot_elimination {n : ℕ}
    (M : (Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)ˣ) :
    ∃ p : Fin (n + 1), ∃ U V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ,
      UpperUnitriangularMatrices.Construction.IsUpperUnitriangular U ∧ UpperUnitriangularMatrices.Construction.IsUpperUnitriangular V ∧
      (U * M.val * V) (Fin.last n) p ≠ 0 ∧
      (∀ j, j ≠ p → (U * M.val * V) (Fin.last n) j = 0) ∧
      (∀ i, i ≠ Fin.last n → (U * M.val * V) i p = 0) := by
  obtain ⟨j, hj⟩ := Split.ExponentialMatrixChamber.Construction.invertible_matrix_row_nonzero M (Fin.last n)
  let S : Finset (Fin (n + 1)) := Finset.univ.filter (fun i => M.val (Fin.last n) i ≠ 0)
  have hS : S.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  let p := S.min' hS
  have hp : M.val (Fin.last n) p ≠ 0 := (Finset.mem_filter.mp (S.min'_mem hS)).2
  have hbefore : ∀ j, j < p → M.val (Fin.last n) j = 0 := by
    intro j hj
    by_contra hn
    exact (not_le_of_gt hj) (S.min'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩))
  let c : Fin (n + 1) → ℝ := fun i => if i = Fin.last n then 0 else -M.val i p / M.val (Fin.last n) p
  let v : Fin (n + 1) → ℝ := fun j => if j = p then 0 else -M.val (Fin.last n) j / M.val (Fin.last n) p
  let U := upperColumnShear c
  let V := upperRowShear p v
  have hU : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular U := upperColumnShear_unitriangular c (by simp [c])
  have hV : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular V := upperRowShear_unitriangular p v (by
    intro j hj
    rcases hj.eq_or_lt with he | he
    · simp [v, he]
    · simp [v, ne_of_lt he, hbefore j he])
  have hlast : ∀ j, (U * M.val) (Fin.last n) j = M.val (Fin.last n) j := by
    intro j
    simp [U, upperColumnShear_mul, c]
  have hcol : ∀ i, i ≠ Fin.last n → (U * M.val) i p = 0 := by
    intro i hi
    rw [upperColumnShear_mul]
    simp [c, hi, div_mul_cancel₀ _ hp]
  refine ⟨p, U, V, hU, hV, ?_, ?_, ?_⟩
  · simpa [V, mul_upperRowShear, hlast, v] using hp
  · intro j hj
    rw [mul_upperRowShear, hlast, hlast]
    dsimp only [v]
    rw [ite_eq_right hj]
    field_simp
    ring
  · intro i hi
    rw [mul_upperRowShear, hcol i hi]
    simp

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.UpperPivotElimination.Construction
