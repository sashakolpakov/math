import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-! # Free Submodule -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.FreeSubmodule

noncomputable section

/-! Every finite module over a domain contains a finite free submodule
of full rank with a single nonzero scalar annihilating the quotient. -/

open _root_.Module

universe u v

theorem exists_submodule (R : Type u) [CommRing R] [IsDomain R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ N : Submodule R M, Module.Free R N ∧ Module.Finite R N ∧
      Module.finrank R N = Module.finrank R M ∧
      ∃ r : R, r ≠ 0 ∧ ∀ x : M ⧸ N, r • x = 0 := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := R) (M := M) (le_refl (Module.finrank R M))
  let N := Submodule.span R (Set.range v)
  let b := Basis.span hv
  let : Module.Free R N := Module.Free.of_basis b
  let : Module.Finite R N := Module.Finite.of_basis b
  have hn : Module.finrank R N = Module.finrank R M := by
    simpa using Module.finrank_eq_card_basis b
  have hq : Module.finrank R (M ⧸ N) = 0 := by
    have h := N.finrank_quotient_add_finrank
    rw [hn] at h
    omega
  have ht : Module.IsTorsion R (M ⧸ N) := Module.finrank_eq_zero_iff_isTorsion.mp hq
  obtain ⟨r, hr, hr0⟩ := Submodule.annihilator_top_inter_nonZeroDivisors ht
  exact ⟨N, inferInstance, inferInstance, hn, r, nonZeroDivisors.ne_zero hr0,
    fun x => (Submodule.mem_annihilator.mp hr) x (Submodule.mem_top)⟩

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Generic.FreeSubmodule
