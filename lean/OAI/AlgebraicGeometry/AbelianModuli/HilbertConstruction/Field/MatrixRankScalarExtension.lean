import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Matrix.KernelDimensionOpen

/-! # Matrix Rank Scalar Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.MatrixRankScalarExtension

noncomputable section

/-! Extending a field preserves matrix rank and the dimension of the actual matrix kernel. -/

universe u

variable {K L : Type u} [Field K] [Field L]
variable {μ ν : Type u} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]

theorem fieldMatrix_rank_map (φ : K →+* L) (A : Matrix ν μ K) : (A.map φ).rank = A.rank := by
  have hq (q : ℕ) : q ≤ (A.map φ).rank ↔ q ≤ A.rank := by
    rw [MatrixLargeMinors.field_matrix_rank_le_iff_large_minor, MatrixLargeMinors.field_matrix_rank_le_iff_large_minor]
    apply exists_congr
    intro r
    apply and_congr_right
    intro _
    apply exists_congr
    intro a
    apply exists_congr
    intro b
    have hz : φ (A.submatrix b a).det = 0 ↔ (A.submatrix b a).det = 0 := by
      simpa only [map_zero] using
        (φ.injective.eq_iff : φ (A.submatrix b a).det = φ 0 ↔ (A.submatrix b a).det = 0)
    exact ((congrArg (fun z : L => z ≠ 0) (φ.map_det (A.submatrix b a)).symm).to_iff).trans
      (not_congr hz)
  exact le_antisymm ((hq _).mp le_rfl) ((hq _).mpr le_rfl)

theorem fieldMatrix_kernel_finrank_map (φ : K →+* L) (A : Matrix ν μ K) :
    Module.finrank L (Matrix.toLin' (A.map φ)).ker = Module.finrank K (Matrix.toLin' A).ker := by
  have hK := HilbertConstruction.Matrix.KernelDimensionOpen.field_matrix_kernel_dimension_add_rank A
  have hL := HilbertConstruction.Matrix.KernelDimensionOpen.field_matrix_kernel_dimension_add_rank (A.map φ)
  have hr := fieldMatrix_rank_map φ A
  omega

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.MatrixRankScalarExtension
