import OAI.NumberTheory.ArithmeticGroups.Lattices.JordanScaling
import OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixJordanDecomposition
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.JordanDescent

/-! # Semisimple Scaling -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.SemisimpleScaling

noncomputable section

/-! The scaling matrix for a nilpotent infinitesimal element may be
chosen semisimple and remains defined over the original field. -/

open scoped Classical

attribute [local instance] LieRing.ofAssociativeRing

variable {F : Type} [Field F] [CharZero F] {n : ℕ}

theorem matrix_semisimple_summand_retains_scaling
    (N S A : Matrix (Fin n) (Fin n) F) (hNS : Commute N S) (hN : IsNilpotent N)
    (hS : Module.End.IsSemisimple (Matrix.toLin' S))
    (hscale : (N + S) * A - A * (N + S) = A) : S * A - A * S = A := by
  let e := Matrix.toLinAlgEquiv' (R := F) (n := Fin n)
  have he : ⁅e N + e S, e A⁆ = (1 : F) • e A := by
    rw [one_smul]
    change (e N + e S) * e A - e A * (e N + e S) = e A
    rw [← map_add, ← map_mul, ← map_mul, ← map_sub, hscale]
  have h := (ArithmeticGroups.Lattices.JordanScaling.Construction.semisimple_summand_retains_bracket_scaling (e N) (e S) (e A)
    (hNS.map e) (hN.map e) hS 1 he).1
  apply e.injective
  simpa only [map_sub, map_mul, one_smul] using! h

theorem infinitesimal_nilpotent_has_semisimple_scaling_matrix
    (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (hG : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    (A : Matrix (Fin n) (Fin n) F) (hA : A ∈ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G) (hnil : IsNilpotent A) :
    ∃ S ∈ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G,
      Module.End.IsSemisimple (Matrix.toLin' S) ∧ S * A - A * S = A := by
  obtain ⟨H, hH, hscale⟩ := ArithmeticGroups.Lattices.JordanScaling.Construction.infinitesimal_nilpotent_has_scaling_matrix G hG hsemi hA hnil
  obtain ⟨N, S, hN, hS, hNS, hHsum⟩ := ArithmeticGroups.Lattices.MatrixJordanDecomposition.Construction.matrix_exists_jordan_decomposition H
  have hmem : N + S ∈ ArithmeticGroups.Lattices.Infinitesimal.Action.Construction.infinitesimalStabilizer G := hHsum ▸ hH
  have hparts := ArithmeticGroups.Lattices.Infinitesimal.JordanDescent.Construction.infinitesimal_jordan_summands G hG N S hN hS hNS hmem
  refine ⟨S, hparts.2, hS, matrix_semisimple_summand_retains_scaling N S A hNS hN hS ?_⟩
  rwa [← hHsum]

end

end OAI.NumberTheory.Quaternion.Arithmetic.SemisimpleScaling
