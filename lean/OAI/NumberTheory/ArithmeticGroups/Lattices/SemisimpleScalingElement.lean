import OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixJordanDecomposition
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.JordanDescent
import OAI.NumberTheory.ArithmeticGroups.Lattices.JordanScaling

/-! # Semisimple Scaling Element -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.SemisimpleScalingElement.Construction

noncomputable section

/-! A rational nilpotent in the semisimple algebraic Lie algebra admits
a rational semisimple infinitesimal scaling element. -/

open scoped Classical

attribute [local instance] LieRing.ofAssociativeRing

theorem infinitesimal_exists_jordan_decomposition
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (hconn : G.IsGeometricallyConnected)
    (A : Matrix (Fin n) (Fin n) k) (hA : A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    ∃ N ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G, ∃ S ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G,
      IsNilpotent N ∧ Module.End.IsSemisimple (Matrix.toLin' S) ∧
        Commute N S ∧ A = N + S := by
  obtain ⟨N, S, hnil, hsemi, hcomm, heq⟩ := MatrixJordanDecomposition.Construction.matrix_exists_jordan_decomposition A
  obtain ⟨hN, hS⟩ := Infinitesimal.JordanDescent.Construction.infinitesimal_jordan_summands G hconn N S hnil hsemi hcomm (heq ▸ hA)
  exact ⟨N, hN, S, hS, hnil, hsemi, hcomm, heq⟩

theorem infinitesimal_nilpotent_has_semisimple_scaling_matrix
    {k : Type} [Field k] [CharZero k] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n)
    (hconn : G.IsGeometricallyConnected) (hsemi : G.IsSemisimple)
    {A : Matrix (Fin n) (Fin n) k} (hA : A ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G)
    (hnil : IsNilpotent A) :
    ∃ S ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G,
      Module.End.IsSemisimple (Matrix.toLin' S) ∧ S * A - A * S = A := by
  obtain ⟨H, hH, hscale⟩ := JordanScaling.Construction.infinitesimal_nilpotent_has_scaling_matrix G hconn hsemi hA hnil
  obtain ⟨N, _, S, hS, hNnil, hSsemi, hNS, hHNS⟩ :=
    infinitesimal_exists_jordan_decomposition G hconn H hH
  refine ⟨S, hS, hSsemi, ?_⟩
  let e : Matrix (Fin n) (Fin n) k ≃ₐ[k] Module.End k (Fin n → k) := Matrix.toLinAlgEquiv'
  have hscale' : ⁅e N + e S, e A⁆ = (1 : k) • e A := by
    change (e N + e S) * e A - e A * (e N + e S) = (1 : k) • e A
    rw [← map_add, ← map_mul, ← map_mul, ← map_sub, ← hHNS, hscale, one_smul]
  have hSscale := (JordanScaling.Construction.semisimple_summand_retains_bracket_scaling
    (e N) (e S) (e A) (hNS.map e) (hNnil.map e) hSsemi 1 hscale').1
  apply e.injective
  simpa only [map_sub, map_mul, Ring.lie_def, one_smul] using hSscale

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.SemisimpleScalingElement.Construction
