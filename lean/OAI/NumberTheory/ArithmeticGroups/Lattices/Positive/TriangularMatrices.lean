import OAI.NumberTheory.ArithmeticGroups.Lattices.UpperUnitriangularMatrices
import OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalOperatorMatrices

/-! # Triangular Matrices -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.TriangularMatrices.Construction

noncomputable section

/-! Positive upper triangular matrices form a subgroup of GL and
meet the orthogonal group only in the identity. -/

open scoped Classical

def IsPositiveUpperTriangular {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  M.IsUpperTriangular ∧ ∀ i, 0 < M i i

theorem IsPositiveUpperTriangular.mul {n : ℕ} {M N : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsPositiveUpperTriangular M) (hN : IsPositiveUpperTriangular N) :
    IsPositiveUpperTriangular (M * N) := by
  refine ⟨hM.1.mul hN.1, fun i => ?_⟩
  rw [UpperUnitriangularMatrices.Construction.upper_triangular_mul_diagonal M N hM.1 hN.1]
  exact mul_pos (hM.2 i) (hN.2 i)

theorem IsPositiveUpperTriangular.unit_inv {n : ℕ} (g : (Matrix (Fin n) (Fin n) ℝ)ˣ)
    (hg : IsPositiveUpperTriangular g.val) : IsPositiveUpperTriangular (g⁻¹).val := by
  let : Invertible g.val := g.invertible
  have htri : (g⁻¹).val.IsUpperTriangular := by
    rw [Matrix.GeneralLinearGroup.coe_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg.1
  refine ⟨htri, fun i => ?_⟩
  have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i i) g.val_inv
  change (g.val * (g⁻¹).val) i i = (1 : Matrix (Fin n) (Fin n) ℝ) i i at he
  rw [UpperUnitriangularMatrices.Construction.upper_triangular_mul_diagonal _ _ hg.1 htri, Matrix.one_apply_eq] at he
  exact (mul_pos_iff_of_pos_left (hg.2 i)).mp (he.symm ▸ zero_lt_one)

theorem positive_upper_triangular_orthogonal_eq_one {n : ℕ}
    (g : (Matrix (Fin n) (Fin n) ℝ)ˣ) (hg : IsPositiveUpperTriangular g.val)
    (ho : g.val ∈ Matrix.orthogonalGroup (Fin n) ℝ) : g = 1 := by
  have hi : (g⁻¹).val = g.val.transpose :=
    g.inv_eq_of_mul_eq_one_right ((Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp ho)
  have ht := (hg.unit_inv g).1
  rw [hi] at ht
  have hz : ∀ i j, i ≠ j → g.val i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact ht h
    · exact hg.1 h
  have hd : ∀ i, g.val i i = 1 := by
    intro i
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i i)
      ((Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp ho)
    rw [UpperUnitriangularMatrices.Construction.upper_triangular_mul_diagonal _ _ hg.1 ht, Matrix.one_apply_eq] at he
    change g.val i i * g.val i i = 1 at he
    nlinarith [hg.2 i]
  apply Units.ext
  ext i j
  by_cases hij : i = j
  · subst j
    exact (hd i).trans (Matrix.one_apply_eq i).symm
  · rw [hz i j hij, Units.val_one, Matrix.one_apply, ite_eq_right hij]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.TriangularMatrices.Construction
