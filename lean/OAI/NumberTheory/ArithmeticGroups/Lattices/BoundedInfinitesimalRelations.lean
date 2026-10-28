import OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedNilpotentAction
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Action

/-! # Bounded Infinitesimal Relations -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedInfinitesimalRelations.Construction

noncomputable section

/-! The bounded polynomial action respects sums and commuting matrices. -/

open scoped Classical

theorem boundedInfinitesimal_add
    {k : Type} [Field k] {n : ℕ} (d : ℕ) (A B : Matrix (Fin n) (Fin n) k) :
    Infinitesimal.Degree.Construction.boundedInfinitesimal d (A + B) = Infinitesimal.Degree.Construction.boundedInfinitesimal d A + Infinitesimal.Degree.Construction.boundedInfinitesimal d B := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  change Infinitesimal.Action.Construction.rightInfinitesimal (A + B) p.val = Infinitesimal.Action.Construction.rightInfinitesimal A p.val + Infinitesimal.Action.Construction.rightInfinitesimal B p.val
  exact congrArg (fun D : Derivation k (Algebraic.CoordinatePolynomial n k) (Algebraic.CoordinatePolynomial n k) => D p.val)
    (Infinitesimal.Action.Construction.rightInfinitesimalLinear.map_add A B)

theorem boundedInfinitesimal_commute
    {k : Type} [Field k] {n : ℕ} (d : ℕ) (A B : Matrix (Fin n) (Fin n) k)
    (hAB : Commute A B) : Commute (Infinitesimal.Degree.Construction.boundedInfinitesimal d A) (Infinitesimal.Degree.Construction.boundedInfinitesimal d B) := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  change Infinitesimal.Action.Construction.rightInfinitesimal A (Infinitesimal.Action.Construction.rightInfinitesimal B p.val) =
    Infinitesimal.Action.Construction.rightInfinitesimal B (Infinitesimal.Action.Construction.rightInfinitesimal A p.val)
  apply sub_eq_zero.mp
  have h := congrArg
    (fun D : Derivation k (Algebraic.CoordinatePolynomial n k) (Algebraic.CoordinatePolynomial n k) => D p.val)
    (Infinitesimal.Action.Construction.rightInfinitesimal_bracket A B)
  have hz : Infinitesimal.Action.Construction.rightInfinitesimal (0 : Matrix (Fin n) (Fin n) k) = 0 := Infinitesimal.Action.Construction.rightInfinitesimalLinear.map_zero
  simpa only [Ring.lie_def, hAB.eq, sub_self, hz, Derivation.zero_apply,
    Derivation.commutator_apply] using h.symm

theorem boundedInfinitesimal_preserves_ideal
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) (d : ℕ)
    (A : Matrix (Fin n) (Fin n) k) (hA : A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    BoundedRepresentation.Construction.boundedIdealSubspace G d ≤ (BoundedRepresentation.Construction.boundedIdealSubspace G d).comap (Infinitesimal.Degree.Construction.boundedInfinitesimal d A) := by
  intro p hp
  exact (Infinitesimal.Action.Construction.mem_infinitesimalStabilizer G A).mp hA p.val hp

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedInfinitesimalRelations.Construction
