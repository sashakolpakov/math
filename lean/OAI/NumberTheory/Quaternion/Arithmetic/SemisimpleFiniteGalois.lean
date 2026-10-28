import OAI.NumberTheory.Quaternion.Arithmetic.FiniteGaloisDiagonalization
import OAI.NumberTheory.ArithmeticGroups.Lattices.SemisimpleMatrixDiagonalization
import OAI.NumberTheory.ArithmeticGroups.Lattices.DiagonalConjugatorNormalization

/-! # Semisimple Finite Galois -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.SemisimpleFiniteGalois

noncomputable section

/-! A semisimple matrix in characteristic zero diagonalizes over a
finite Galois extension, with a determinant-one conjugating matrix. -/

open scoped Classical

theorem semisimple_matrix_finiteGalois_diagonalization
    {F : Type} [Field F] [CharZero F] {n : ℕ} [Nonempty (Fin n)]
    (S : Matrix (Fin n) (Fin n) F) (hS : Module.End.IsSemisimple (Matrix.toLin' S)) :
    ∃ L : FiniteGaloisIntermediateField F (AlgebraicClosure F),
      ∃ B : Matrix.SpecialLinearGroup (Fin n) L, ∃ w : Fin n → L,
        S.map (algebraMap F L) = (B : Matrix (Fin n) (Fin n) L) * Matrix.diagonal w *
          ((B⁻¹ : Matrix.SpecialLinearGroup (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
  have h := ArithmeticGroups.Lattices.SemisimpleMatrixDiagonalization.Construction.semisimple_matrix_coefficient_map (algebraMap F (AlgebraicClosure F)) S hS
  obtain ⟨g, w, hg⟩ := ArithmeticGroups.Lattices.SemisimpleMatrixDiagonalization.Construction.semisimple_matrix_conjugate_diagonal _ h
  obtain ⟨B, hB⟩ := ArithmeticGroups.Lattices.DiagonalConjugatorNormalization.Construction.diagonal_conjugator_normalization g
  exact FiniteGaloisDiagonalization.exists_finiteGalois_diagonalization S B w (hg.trans (hB w).symm)

end

end OAI.NumberTheory.Quaternion.Arithmetic.SemisimpleFiniteGalois
