import Mathlib.LinearAlgebra.JordanChevalley

/-! # Jordan Invariant Subspace -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.JordanInvariantSubspace.Construction

noncomputable section

/-! Each Jordan component preserves every invariant subspace of the
original endomorphism. -/

open scoped Classical

theorem semisimple_summand_mem_adjoin
    {k V : Type*} [Field k] [PerfectField k] [AddCommGroup V] [Module k V]
    [Module.Finite k V] (N S : Module.End k V)
    (hN : IsNilpotent N) (hS : S.IsSemisimple) (hNS : Commute N S) :
    S ∈ Algebra.adjoin k {N + S} := by
  obtain ⟨N', hN', S', hS', hnil, hsemi, heq⟩ :=
    (N + S).exists_isNilpotent_isSemisimple
  have hcomm : Commute N' S' :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hS'
      (Algebra.commute_of_mem_adjoin_self hN').symm
  have hSS' := (Module.End.isNilpotent_isSemisimple_unique hN hS hnil hsemi hNS hcomm heq).2
  exact hSS'.symm ▸ hS'

theorem semisimple_summand_preserves_submodule
    {k V : Type*} [Field k] [PerfectField k] [AddCommGroup V] [Module k V]
    [Module.Finite k V] (N S : Module.End k V)
    (hN : IsNilpotent N) (hS : S.IsSemisimple) (hNS : Commute N S)
    (W : Submodule k V) (hW : W ≤ W.comap (N + S)) : W ≤ W.comap S := by
  obtain ⟨p, hp⟩ := Algebra.adjoin_mem_exists_aeval k _ (semisimple_summand_mem_adjoin N S hN hS hNS)
  intro x hx
  change S x ∈ W
  rw [← hp]
  exact Polynomial.aeval_apply_smul_mem_of_le_comap hx p (N + S) hW

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.JordanInvariantSubspace.Construction
