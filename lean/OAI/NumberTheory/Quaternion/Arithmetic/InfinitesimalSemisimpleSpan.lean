import OAI.NumberTheory.Quaternion.Arithmetic.SemisimpleScaling
import OAI.NumberTheory.Quaternion.Arithmetic.SemisimplePerturbation

/-! # Infinitesimal Semisimple Span -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.InfinitesimalSemisimpleSpan

noncomputable section

/-! The rational Lie algebra of a connected semisimple matrix group
is spanned by its semisimple matrices. Nilpotent matrices are differences
of two semisimple infinitesimal matrices defined over the same field. -/

open scoped Classical

attribute [local instance] LieRing.ofAssociativeRing

variable {F : Type} [Field F] [CharZero F] {n : ℕ}

def semisimpleInfinitesimalMatrices (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) :
    Set (Matrix (Fin n) (Fin n) F) :=
  {S | S ∈ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G ∧ Module.End.IsSemisimple (Matrix.toLin' S)}

theorem nilpotent_infinitesimal_mem_semisimple_span
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (N : Matrix (Fin n) (Fin n) F) (hLie : N ∈ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G) (hN : IsNilpotent N) :
    N ∈ Submodule.span F (semisimpleInfinitesimalMatrices G) := by
  obtain ⟨S, hSLie, hS, hscale⟩ :=
    SemisimpleScaling.infinitesimal_nilpotent_has_semisimple_scaling_matrix G hG hsemi N hLie hN
  have hSspan : S ∈ Submodule.span F (semisimpleInfinitesimalMatrices G) :=
    Submodule.subset_span ⟨hSLie, hS⟩
  have hTspan : S - N ∈ Submodule.span F (semisimpleInfinitesimalMatrices G) :=
    Submodule.subset_span ⟨(ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G).sub_mem hSLie hLie,
      SemisimplePerturbation.semisimple_sub_nilpotent_of_scaling S N hS hN hscale⟩
  simpa only [sub_sub_cancel] using
    (Submodule.span F (semisimpleInfinitesimalMatrices G)).sub_mem hSspan hTspan

theorem infinitesimalStabilizer_eq_span_semisimple
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple) :
    (ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G).toSubmodule = Submodule.span F (semisimpleInfinitesimalMatrices G) := by
  apply le_antisymm
  · intro X hX
    obtain ⟨N, S, hN, hS, hNS, hsum⟩ := ArithmeticGroups.Lattices.MatrixJordanDecomposition.Construction.matrix_exists_jordan_decomposition X
    have hparts := ArithmeticGroups.Lattices.Infinitesimal.JordanDescent.Construction.infinitesimal_jordan_summands G hG N S hN hS hNS (hsum ▸ hX)
    rw [hsum]
    exact (Submodule.span F (semisimpleInfinitesimalMatrices G)).add_mem
      (nilpotent_infinitesimal_mem_semisimple_span G hG hsemi N hparts.1 hN)
      (Submodule.subset_span ⟨hparts.2, hS⟩)
  · exact Submodule.span_le.mpr (fun _ h => h.1)

end

end OAI.NumberTheory.Quaternion.Arithmetic.InfinitesimalSemisimpleSpan
