import OAI.NumberTheory.ArithmeticGroups.Lattices.SemisimpleMatrixDiagonalization
import OAI.NumberTheory.ArithmeticGroups.Lattices.JordanInvariantSubspace

/-! # Matrix Jordan Decomposition -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixJordanDecomposition.Construction

noncomputable section

/-! The Jordan decomposition in concrete matrix coordinates. -/

open scoped Classical

theorem matrix_exists_jordan_decomposition
    {k : Type} [Field k] [PerfectField k] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) :
    ∃ N S : Matrix (Fin n) (Fin n) k,
      IsNilpotent N ∧ Module.End.IsSemisimple (Matrix.toLin' S) ∧
        Commute N S ∧ A = N + S := by
  let f : Module.End k (Fin n → k) := Matrix.toLin' A
  obtain ⟨N, hN, S, hS, hnil, hsemi, heq⟩ := f.exists_isNilpotent_isSemisimple
  have hcomm : Commute N S :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hS
      (Algebra.commute_of_mem_adjoin_self hN).symm
  let e : Module.End k (Fin n → k) ≃ₐ[k] Matrix (Fin n) (Fin n) k :=
    LinearMap.toMatrixAlgEquiv'
  refine ⟨e N, e S, hnil.map e, ?_, hcomm.map e, ?_⟩
  · change Module.End.IsSemisimple (Matrix.toLin' (LinearMap.toMatrix' S))
    rwa [Matrix.toLin'_toMatrix']
  · change A = LinearMap.toMatrix' N + LinearMap.toMatrix' S
    have h := congrArg LinearMap.toMatrix' heq
    simpa only [map_add, f, LinearMap.toMatrix'_toLin'] using h

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixJordanDecomposition.Construction
