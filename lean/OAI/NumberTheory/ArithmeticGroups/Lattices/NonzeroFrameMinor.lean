import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! # Nonzero Frame Minor -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.NonzeroFrameMinor.Construction

noncomputable section

/-! An independent rectangular frame has a nonzero maximal minor. -/

open scoped Classical
open _root_.Module

theorem exists_nonzero_frame_minor
    {k : Type*} [Field k] {n r : ℕ} (U : Matrix (Fin n) (Fin r) k)
    (hU : LinearIndependent k (fun j => fun i => U i j)) :
    ∃ rows : Fin r → Fin n, (U.submatrix rows id).det ≠ 0 := by
  obtain ⟨κ, a, _, hspan, hlin⟩ := exists_linearIndependent' k U.row
  let : Finite κ := hlin.finite
  let : Fintype κ := Fintype.ofFinite κ
  have hcols : LinearIndependent k U.col := hU
  have hcard : Fintype.card κ = r := by
    rw [← finrank_span_eq_card hlin, hspan, ← Matrix.rank_eq_finrank_span_row,
      Matrix.rank_eq_finrank_span_cols, finrank_span_eq_card hcols, Fintype.card_fin]
  let e : Fin r ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨a ∘ e, ?_⟩
  have hl : LinearIndependent k (U.submatrix (a ∘ e) id).row := hlin.comp e e.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hl)).ne_zero

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.NonzeroFrameMinor.Construction
