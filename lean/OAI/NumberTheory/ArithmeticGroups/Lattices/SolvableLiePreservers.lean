import OAI.NumberTheory.ArithmeticGroups.Lattices.LieInvariantSubspaces

/-! # Solvable Lie Preservers -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.SolvableLiePreservers.Construction

noncomputable section

/-! A faithful linear group preserving all invariant subspaces of a
solvable Lie algebra is solvable. -/

open scoped Classical

universe u

theorem group_solvable_of_preserves_lie_submodules
    {k L : Type*} {V H : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    [LieRing L] [LieAlgebra k L] [LieAlgebra.IsSolvable L]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [LieRingModule L V] [LieModule k L V] [Group H]
    (ρ : H →* (V ≃ₗ[k] V)) (hρ : Function.Injective ρ)
    (hstable : ∀ W : LieSubmodule k L V, ∀ g x, x ∈ W → ρ g x ∈ W) :
    Group.IsSolvable H := by
  induction hd : Module.finrank k V using Nat.strong_induction_on generalizing V H with
  | h d ih =>
    by_cases hV : Subsingleton V
    · let : Subsingleton V := hV
      let : Subsingleton H := hρ.subsingleton
      exact Group.isSolvable_of_comm (fun a b : H => Subsingleton.elim (a * b) (b * a))
    · let : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
      obtain ⟨W, hdimW⟩ := LieInvariantSubspaces.Construction.exists_lie_invariant_line (k := k) (L := L) (V := V)
      have hW : ∀ g, W.toSubmodule.map (ρ g).toLinearMap = W.toSubmodule :=
        LieInvariantSubspaces.Construction.invariant_map_eq_of_mem ρ W.toSubmodule (hstable W)
      let r := LieInvariantSubspaces.Construction.invariantRestriction ρ W.toSubmodule hW
      let q := LieInvariantSubspaces.Construction.invariantQuotient ρ W.toSubmodule hW
      have hr : Group.IsSolvable r.range := by
        apply Group.isSolvable_of_comm
        intro e f
        apply Subtype.ext
        exact LieInvariantSubspaces.Construction.linearEquiv_comm_of_finrank_one hdimW e.val f.val
      have hlt : Module.finrank k (V ⧸ W) < d := by
        have hh := W.toSubmodule.finrank_quotient_add_finrank
        change Module.finrank k (V ⧸ W) + Module.finrank k W = Module.finrank k V at hh
        omega
      have hq : Group.IsSolvable q.range := by
        apply ih (Module.finrank k (V ⧸ W)) hlt (V := V ⧸ W) (H := q.range) q.range.subtype
          q.range.subtype_injective
        · exact LieInvariantSubspaces.Construction.quotient_preserves_lie_submodules ρ hstable W hW
        · rfl
      let : Group.IsSolvable r.range := hr
      let : Group.IsSolvable q.range := hq
      exact LieInvariantSubspaces.Construction.linear_group_solvable_of_subquotient ρ hρ W.toSubmodule hW

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.SolvableLiePreservers.Construction
