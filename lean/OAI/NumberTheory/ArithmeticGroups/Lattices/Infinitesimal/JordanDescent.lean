import OAI.NumberTheory.ArithmeticGroups.Lattices.AlgebraicallyClosedJordanStability
import OAI.NumberTheory.ArithmeticGroups.Lattices.SemisimpleMatrixDiagonalization
import OAI.NumberTheory.ArithmeticGroups.Lattices.CharZeroTangent

/-! # Jordan Descent -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.JordanDescent.Construction

noncomputable section

/-! Jordan components of infinitesimal matrices are defined over the
original characteristic-zero field and remain in the Lie algebra. -/

open scoped Classical

attribute [local instance] LieRing.ofAssociativeRing

theorem infinitesimalStabilizer_descends_coefficient_map
    {k K : Type} [Field k] [CharZero k] [Field K] {n : ℕ}
    (ι : k →+* K) (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (A : Matrix (Fin n) (Fin n) k)
    (hA : A.map ι ∈ Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G ι)) :
    A ∈ Action.Construction.infinitesimalStabilizer G := by
  apply (CharZeroTangent.Construction.mem_infinitesimalStabilizer_iff_tangent G hG A).mpr
  intro p hp
  apply ι.injective
  rw [map_zero, ← CoefficientMap.Construction.tangent_coefficient_map]
  have h := (Action.Construction.mem_infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G ι) _).mp hA _
    (BaseChange.Construction.coefficient_map_mem_baseChange_vanishingIdeal G ι hp)
  exact h K (RingHom.id K) (1 : (BaseChange.Construction.matrixGroupBaseChange G ι).RationalPoints)

theorem infinitesimal_jordan_summands
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hG : G.IsGeometricallyConnected)
    (N S : Matrix (Fin n) (Fin n) k)
    (hN : IsNilpotent N) (hS : Module.End.IsSemisimple (Matrix.toLin' S))
    (hNS : Commute N S) (hmem : N + S ∈ Action.Construction.infinitesimalStabilizer G) :
    N ∈ Action.Construction.infinitesimalStabilizer G ∧ S ∈ Action.Construction.infinitesimalStabilizer G := by
  let K := AlgebraicClosure k
  let ι := algebraMap k K
  have hnil : IsNilpotent (N.map ι) := hN.map ι.mapMatrix
  have hsemi : Module.End.IsSemisimple (Matrix.toLin' (S.map ι)) :=
    SemisimpleMatrixDiagonalization.Construction.semisimple_matrix_coefficient_map ι S hS
  have hcomm : Commute (N.map ι) (S.map ι) := hNS.map ι.mapMatrix
  have hsum : N.map ι + S.map ι ∈ Action.Construction.infinitesimalStabilizer (BaseChange.Construction.matrixGroupBaseChange G ι) := by
    convert CharZeroTangent.Construction.infinitesimalStabilizer_coefficient_map (K := K) G hG hmem using 1
    exact (ι.mapMatrix.map_add N S).symm
  obtain ⟨hN', hS'⟩ := AlgebraicallyClosedJordanStability.Construction.infinitesimal_jordan_summands_of_algClosed
    (BaseChange.Construction.matrixGroupBaseChange G ι) (N.map ι) (S.map ι) hnil hsemi hcomm hsum
  exact ⟨infinitesimalStabilizer_descends_coefficient_map ι G hG N hN',
    infinitesimalStabilizer_descends_coefficient_map ι G hG S hS'⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.JordanDescent.Construction
