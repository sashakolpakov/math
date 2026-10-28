import OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.InvariantSystem
import OAI.NumberTheory.ArithmeticGroups.Lattices.AveragedGramMatrix
import OAI.NumberTheory.ArithmeticGroups.Lattices.RationalSubspaceDensity

/-! # Form Descent -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.FormDescent.Construction

noncomputable section

/-! A finite bilinear invariance system defined over a subfield of the
reals has a positive solution over that subfield whenever it has a
positive real solution. -/

open scoped Classical _root_.Matrix.Norms.Elementwise
open _root_.Matrix Set

theorem positive_matrix_descends_in_subspace
    {k : Type} [Field k] [CharZero k] [Algebra k ℝ] {n : ℕ}
    (W : Submodule k (Matrix (Fin n) (Fin n) k))
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q ∈ MatrixFlatExtension.Construction.matrixSubspaceExtension (K := ℝ) W)
    (hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < dotProduct x (Q.mulVec x)) :
    ∃ q ∈ W, ∀ x : Fin n → ℝ, x ≠ 0 →
      0 < dotProduct x ((q.map (algebraMap k ℝ)).mulVec x) := by
  have hc := RationalSubspaceDensity.Construction.matrixSubspaceExtension_subset_closure W hQ
  obtain ⟨R, hRpos, q, hq, hqR⟩ := mem_closure_iff.mp hc _
    (AveragedGramMatrix.Construction.isOpen_positive_quadratic_matrices n) hpos
  subst R
  exact ⟨q, hq, hRpos⟩

theorem positive_bilinear_system_solution_descends
    {k ι : Type} [Field k] [CharZero k] [Algebra k ℝ] [Fintype ι] {n : ℕ}
    (A : ι → Matrix (Fin n) (Fin n) k)
    (Q : Matrix (Fin n) (Fin n) ℝ)
    (hinv : ∀ i, Bilinear.InvariantSystem.Construction.bilinearLieVariation ((A i).map (algebraMap k ℝ)) Q = 0)
    (hpos : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < dotProduct x (Q.mulVec x)) :
    ∃ q : Matrix (Fin n) (Fin n) k,
      (∀ i, Bilinear.InvariantSystem.Construction.bilinearLieVariation (A i) q = 0) ∧
      ∀ x : Fin n → ℝ, x ≠ 0 → 0 < dotProduct x ((q.map (algebraMap k ℝ)).mulVec x) := by
  have hker : Q ∈ MatrixFlatExtension.Construction.matrixSubspaceExtension (K := ℝ) (Bilinear.InvariantSystem.Construction.bilinearInvariantSystem A).ker := by
    rw [Bilinear.InvariantSystem.Construction.bilinearInvariantSystem_kernel_baseChange]
    change Bilinear.InvariantSystem.Construction.bilinearInvariantSystem _ Q = 0
    funext t
    exact congrArg (fun M => M t.2.1 t.2.2) (hinv t.1)
  obtain ⟨q, hq, hp⟩ := positive_matrix_descends_in_subspace (Bilinear.InvariantSystem.Construction.bilinearInvariantSystem A).ker Q hker hpos
  refine ⟨q, ?_, hp⟩
  intro i
  ext a b
  exact congrFun hq (i, a, b)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.FormDescent.Construction
