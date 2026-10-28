import OAI.NumberTheory.PadicHodge.GeometricComparison.Linear

/-! # Subspace Base Change Stability -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SubspaceBaseChangeStability.SubspaceBaseChange

noncomputable section

/-! Field extension preserves the actual invariant subspaces of linear operators. -/

open scoped TensorProduct

variable {K L V : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup V] [Module K V]

theorem stable (P : Submodule K V) (T : Module.End K V) (h : P ≤ P.comap T) :
    P.baseChange L ≤ (P.baseChange L).comap (T.baseChange L) := by
  refine (P.baseChange_eq_span L).le.trans (Submodule.span_le.mpr ?_)
  rintro x ⟨v, hv, rfl⟩
  change (1 : L) ⊗ₜ[K] T v ∈ P.baseChange L
  exact P.tmul_mem_baseChange_of_mem 1 (h hv)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SubspaceBaseChangeStability.SubspaceBaseChange
