import OAI.NumberTheory.ArithmeticGroups.Lattices.SemisimpleMatrixDiagonalization
import Mathlib.RingTheory.Polynomial.Basic

/-! # Annihilator -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Split.Annihilator.Construction

noncomputable section

/-! A product of distinct linear factors annihilating an endomorphism
gives a decomposition into eigenspaces over the coefficient field. -/

open scoped Classical
open _root_.Polynomial

theorem eigenspace_eq_ker_linear_aeval
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (f : Module.End k V) (a : k) :
    f.eigenspace a = LinearMap.ker (Polynomial.aeval f (X - C a)) := by
  rw [map_sub, aeval_X, aeval_C]
  exact Module.End.eigenspace_def.trans (by rw [Algebra.algebraMap_eq_smul_one])

theorem finite_eigenspace_sup_eq_ker
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (f : Module.End k V) (s : Finset k) :
    s.sup f.eigenspace = LinearMap.ker (Polynomial.aeval f (∏ a ∈ s, (X - C a))) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sup_empty, Finset.prod_empty, map_one]
    exact LinearMap.ker_id.symm
  | @insert a s ha ih =>
    have hc : IsCoprime (X - C a) (∏ b ∈ s, (X - C b)) := by
      apply IsCoprime.prod_right
      intro b hb
      apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      have hab : a ≠ b := fun h => ha (h.symm ▸ hb)
      exact (sub_ne_zero.mpr hab).isUnit
    rw [Finset.sup_insert, Finset.prod_insert ha, ih, eigenspace_eq_ker_linear_aeval,
      Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hc]

theorem eigenspaces_span_of_split_annihilator
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (f : Module.End k V) (s : Finset k)
    (hf : Polynomial.aeval f (∏ a ∈ s, (X - C a)) = 0) :
    (⨆ a, f.eigenspace a) = ⊤ := by
  have hs : s.sup f.eigenspace = ⊤ := by
    rw [finite_eigenspace_sup_eq_ker, hf, LinearMap.ker_zero]
  apply top_unique
  rw [← hs]
  exact Finset.sup_le (fun a _ => le_iSup f.eigenspace a)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Split.Annihilator.Construction
