import OAI.NumberTheory.ArithmeticGroups.Lattices.SemisimpleMatrixDiagonalization
import OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedInfinitesimalRelations
import OAI.NumberTheory.ArithmeticGroups.Lattices.JordanInvariantSubspace

/-! # Algebraically Closed Jordan Stability -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.AlgebraicallyClosedJordanStability.Construction

noncomputable section

/-! Over an algebraically closed field, the semisimple and nilpotent
matrix Jordan components preserve the group's defining ideal. -/

open scoped Classical

attribute [local instance] LieRing.ofAssociativeRing

theorem infinitesimal_semisimple_summand_of_algClosed
    {k : Type} [Field k] [IsAlgClosed k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (N S : Matrix (Fin n) (Fin n) k)
    (hN : IsNilpotent N) (hS : Module.End.IsSemisimple (Matrix.toLin' S))
    (hNS : Commute N S) (hG : N + S ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    S ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G := by
  apply (Infinitesimal.Action.Construction.mem_infinitesimalStabilizer G S).mpr
  intro p hp
  let d := p.totalDegree
  let q : BoundedRepresentation.Construction.BoundedPolynomials k n d :=
    ⟨p, (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr le_rfl⟩
  have hstable : BoundedRepresentation.Construction.boundedIdealSubspace G d ≤
      (BoundedRepresentation.Construction.boundedIdealSubspace G d).comap (Infinitesimal.Degree.Construction.boundedInfinitesimal d S) := by
    apply JordanInvariantSubspace.Construction.semisimple_summand_preserves_submodule (k := k)
      (V := BoundedRepresentation.Construction.BoundedPolynomials k n d)
      (Infinitesimal.Degree.Construction.boundedInfinitesimal d N) (Infinitesimal.Degree.Construction.boundedInfinitesimal d S)
      (BoundedNilpotentAction.Construction.boundedInfinitesimal_isNilpotent d N hN)
      (SemisimpleMatrixDiagonalization.Construction.boundedInfinitesimal_isSemisimple_of_algClosed d S hS)
      (BoundedInfinitesimalRelations.Construction.boundedInfinitesimal_commute d N S hNS)
    rw [← BoundedInfinitesimalRelations.Construction.boundedInfinitesimal_add]
    exact BoundedInfinitesimalRelations.Construction.boundedInfinitesimal_preserves_ideal G d (N + S) hG
  have hq : q ∈ BoundedRepresentation.Construction.boundedIdealSubspace G d := hp
  have hSq : Infinitesimal.Degree.Construction.boundedInfinitesimal d S q ∈ BoundedRepresentation.Construction.boundedIdealSubspace G d := hstable hq
  exact hSq

theorem infinitesimal_jordan_summands_of_algClosed
    {k : Type} [Field k] [IsAlgClosed k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (N S : Matrix (Fin n) (Fin n) k)
    (hN : IsNilpotent N) (hS : Module.End.IsSemisimple (Matrix.toLin' S))
    (hNS : Commute N S) (hG : N + S ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    N ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G ∧ S ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G := by
  have hS' := infinitesimal_semisimple_summand_of_algClosed G N S hN hS hNS hG
  exact ⟨by simpa only [add_sub_cancel_right] using (Infinitesimal.Action.Construction.infinitesimalStabilizer G).sub_mem hG hS', hS'⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.AlgebraicallyClosedJordanStability.Construction
