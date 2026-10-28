import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparseFiniteProjectiveFrames
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Sparse Dual Evaluation Frames -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparseDualEvaluationFrames

noncomputable section

/-! A sparsity bound on the zero evaluations of every nonzero vector
gives a projective frame among the actual evaluation functionals. -/
open scoped Classical
universe u v
variable {K V : Type u} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
variable {ι : Type v} [Fintype ι] (e : ι → Module.Dual K V)

theorem dualEvaluation_family_sparse
    (hs : ∀ v : V, v ≠ 0 → Module.finrank K V *
      (Finset.univ.filter (fun i => e i v = 0)).card < Fintype.card ι)
    (W : Submodule K (Module.Dual K V)) (hW : W ≠ ⊤) :
    Module.finrank K (Module.Dual K V) *
      (Finset.univ.filter (fun i => e i ∈ W)).card < Fintype.card ι := by
  obtain ⟨φ, hφ, hker⟩ := W.exists_dual_map_eq_bot_of_lt_top hW.lt_top inferInstance
  let v := (Module.evalEquiv K V).symm φ
  have hv : v ≠ 0 := by
    intro hz
    apply hφ
    have := congrArg (Module.evalEquiv K V) hz
    simpa only [v, LinearEquiv.apply_symm_apply, map_zero] using this
  have hsub : Finset.univ.filter (fun i => e i ∈ W) ⊆
      Finset.univ.filter (fun i => e i v = 0) := by
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [show e i v = φ (e i) from Module.apply_evalEquiv_symm_apply K V _ _]
    have hm : φ (e i) ∈ W.map φ := ⟨e i, (Finset.mem_filter.mp hi).2, rfl⟩
    rwa [hker, Submodule.mem_bot] at hm
  rw [Subspace.dual_finrank_eq]
  exact (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)).trans_lt (hs v hv)

theorem dualEvaluation_projectiveFrame (hp : 0 < Module.finrank K V)
    (hs : ∀ v : V, v ≠ 0 → Module.finrank K V *
      (Finset.univ.filter (fun i => e i v = 0)).card < Fintype.card ι) :
    ∃ (κ : Type u) (_ : Fintype κ) (b : Module.Basis κ K (Module.Dual K V)),
      Set.range b ⊆ Set.range e ∧ ∃ j : ι, ∀ k, b.repr (e j) k ≠ 0 := by
  apply SparseFiniteProjectiveFrames.sparseFiniteFamily_projectiveFrame e
  · simpa only [Subspace.dual_finrank_eq] using hp
  · exact dualEvaluation_family_sparse e hs

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SparseDualEvaluationFrames
