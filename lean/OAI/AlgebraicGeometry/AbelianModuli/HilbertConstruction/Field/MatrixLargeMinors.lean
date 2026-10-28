import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.FlatMatrixPivotCover
import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Matrix Large Minors -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.MatrixLargeMinors

noncomputable section

/-! A lower bound on the rank of a finite matrix over a field is equivalent to the existence of a nonzero coordinate minor of at least that size. -/

universe u

variable {K : Type u} [Field K] {μ ν : Type u} [Fintype μ] [Fintype ν] [DecidableEq μ] [DecidableEq ν]

omit [DecidableEq ν] in
theorem field_matrix_cokernel_dimension_add_rank (A : Matrix ν μ K) :
    Module.finrank K ((ν → K) ⧸ (Matrix.toLin' A).range) + A.rank = Fintype.card ν := by
  change Module.finrank K ((ν → K) ⧸ (Matrix.toLin' A).range) +
    Module.finrank K (Matrix.toLin' A).range = Fintype.card ν
  exact (Submodule.finrank_quotient_add_finrank (Matrix.toLin' A).range).trans
    (Module.finrank_fintype_fun_eq_card K)

theorem field_matrix_rank_le_iff_large_minor (A : Matrix ν μ K) (q : ℕ) :
    q ≤ A.rank ↔ ∃ (r : ℕ), q ≤ r ∧ ∃ (a : Fin r → μ) (b : Fin r → ν), (A.submatrix b a).det ≠ 0 := by
  classical
  constructor
  · intro hq
    obtain ⟨r, a, b, _, _, hu, _, hr⟩ :=
      HilbertScheme.Presentations.Local.FlatMatrixPivotCover.Grassmannian.local_flat_matrix_pivot_cover_rank A
        (Module.finrank K ((ν → K) ⧸ (Matrix.toLin' A).range)) rfl
    have hd := field_matrix_cokernel_dimension_add_rank A
    exact ⟨r, by omega, a, b, hu.ne_zero⟩
  · rintro ⟨r, hqr, a, b, hdet⟩
    have hm : (A.submatrix b a).rank = r := by
      simpa only [Fintype.card_fin] using Matrix.rank_of_det_ne_zero hdet
    have hle := Matrix.rank_submatrix_le A b a
    omega

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.MatrixLargeMinors
