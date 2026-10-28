import OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixDifferential
import OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialHullGroup

/-! # Differential Hull Invariant -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialHullInvariant.Construction

noncomputable section

/-! The algebraic hull preserves every vector subspace preserved by the
original matrix directions. -/

open scoped Classical

theorem invariant_functionalPolynomial_mem_core
    {k : Type} [Field k] {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) k))
    (W : Submodule k (Fin n → k))
    (hW : ∀ A ∈ S, ∀ w ∈ W, A.mulVec w ∈ W)
    (φ : Module.Dual k (Fin n → k)) (hφ : φ ∈ W.dualAnnihilator)
    {w : Fin n → k} (hw : w ∈ W) :
    MatrixDifferential.Construction.matrixFunctionalPolynomial φ w ∈ MatrixDifferential.Construction.matrixDifferentialCore S := by
  apply Ideal.mem_iInf.mpr
  intro m
  induction m generalizing w with
  | zero =>
      change Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (MatrixDifferential.Construction.matrixFunctionalPolynomial φ w) = 0
      rw [MatrixDifferential.Construction.evaluate_matrixFunctionalPolynomial]
      change φ ((1 : Matrix (Fin n) (Fin n) k).mulVec w) = 0
      rw [Matrix.one_mulVec]
      exact (Submodule.mem_dualAnnihilator _).mp hφ w hw
  | succ m ih =>
      refine ⟨ih hw, ?_⟩
      rintro D ⟨A, hA, rfl⟩
      rw [MatrixDifferential.Construction.derivative_matrixFunctionalPolynomial]
      exact ih (hW A hA w hw)

theorem differentialHull_preserves_subspace
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (S : Set (Matrix (Fin n) (Fin n) k)) (W : Submodule k (Fin n → k))
    (hW : ∀ A ∈ S, ∀ w ∈ W, A.mulVec w ∈ W)
    (g : DifferentialHullGroup.Construction.differentialHullSubgroup G S) {w : Fin n → k} (hw : w ∈ W) :
    (g.val.val : Matrix (Fin n) (Fin n) k).mulVec w ∈ W := by
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mp
  intro φ hφ
  have hp := invariant_functionalPolynomial_mem_core S W hW φ hφ hw
  have he := g.property (MatrixDifferential.Construction.matrixFunctionalPolynomial φ w) hp
  rwa [MatrixDifferential.Construction.evaluate_matrixFunctionalPolynomial] at he

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialHullInvariant.Construction
