import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Degree

/-! # Bounded Nilpotent Action -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedNilpotentAction.Construction

noncomputable section

/-! The bounded polynomial representation of a nilpotent matrix is
nilpotent as a finite-dimensional endomorphism. -/

open scoped Classical

theorem finiteDimensional_nilpotent_of_locally_nilpotent
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]
    (f : Module.End k V) (hf : ∀ x, ∃ r : ℕ, (f ^ r) x = 0) : IsNilpotent f := by
  let b := Module.finBasis k V
  choose r hr using fun i => hf (b i)
  refine ⟨∑ i, r i, b.ext fun i => ?_⟩
  have hi : r i ≤ ∑ j, r j := Finset.single_le_sum (fun j _ => Nat.zero_le (r j)) (Finset.mem_univ i)
  change (f ^ ∑ j, r j) (b i) = 0
  rw [← Nat.sub_add_cancel hi, pow_add, Module.End.mul_apply, hr, map_zero]

theorem boundedInfinitesimal_pow_coe
    {k : Type} [Field k] {n d : ℕ} (A : Matrix (Fin n) (Fin n) k)
    (r : ℕ) (p : BoundedRepresentation.Construction.BoundedPolynomials k n d) :
    ((Infinitesimal.Degree.Construction.boundedInfinitesimal d A ^ r) p).val = ((Infinitesimal.Action.Construction.rightInfinitesimal A).toLinearMap ^ r) p.val := by
  induction r with
  | zero => rfl
  | succ r hr =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    change Infinitesimal.Action.Construction.rightInfinitesimal A (((Infinitesimal.Degree.Construction.boundedInfinitesimal d A ^ r) p).val) =
      Infinitesimal.Action.Construction.rightInfinitesimal A (((Infinitesimal.Action.Construction.rightInfinitesimal A).toLinearMap ^ r) p.val)
    rw [hr]

theorem boundedInfinitesimal_isNilpotent
    {k : Type} [Field k] {n : ℕ} (d : ℕ) (A : Matrix (Fin n) (Fin n) k) (hA : IsNilpotent A) :
    IsNilpotent (Infinitesimal.Degree.Construction.boundedInfinitesimal d A) := by
  apply finiteDimensional_nilpotent_of_locally_nilpotent
  intro p
  obtain ⟨r, hr⟩ := LocallyNilpotentDerivation.Construction.nilpotent_matrix_locally_nilpotent_infinitesimal A hA p.val
  refine ⟨r, Subtype.ext ?_⟩
  rw [boundedInfinitesimal_pow_coe]
  exact hr

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedNilpotentAction.Construction
