import OAI.NumberTheory.Quaternion.Arithmetic.NilpotentDerivationExp
import OAI.NumberTheory.ArithmeticGroups.Lattices.JordanScaling
import OAI.NumberTheory.ArithmeticGroups.Lattices.SemisimpleMatrixDiagonalization

/-! # Semisimple Perturbation -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.SemisimplePerturbation

noncomputable section

/-! If a semisimple matrix scales a nilpotent matrix by commutator,
subtracting the nilpotent matrix preserves semisimplicity. -/

open scoped Classical
open _root_.Matrix

attribute [local instance] LieRing.ofAssociativeRing

variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

omit [CharZero F] in
theorem matrix_algHom_preserves_semisimple
    (φ : Matrix (Fin n) (Fin n) F →ₐ[F] Matrix (Fin n) (Fin n) F)
    (S : Matrix (Fin n) (Fin n) F) (hS : Module.End.IsSemisimple (Matrix.toLin' S)) :
    Module.End.IsSemisimple (Matrix.toLin' (φ S)) := by
  let p := minpoly F (Matrix.toLin' S)
  have hp : Squarefree p := hS.minpoly_squarefree
  have hz : Polynomial.aeval S p = 0 := by
    apply Matrix.toLinAlgEquiv'.injective
    rw [← Polynomial.aeval_algHom_apply, map_zero]
    exact minpoly.aeval F (Matrix.toLin' S)
  have hφ : Polynomial.aeval (φ S) p = 0 := by
    rw [Polynomial.aeval_algHom_apply, hz, map_zero]
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp
  change Polynomial.aeval (Matrix.toLinAlgEquiv' (φ S)) p = 0
  rw [Polynomial.aeval_algHom_apply, hφ, map_zero]

theorem semisimple_sub_nilpotent_of_scaling
    (S N : Matrix (Fin n) (Fin n) F) (hS : Module.End.IsSemisimple (Matrix.toLin' S))
    (hN : IsNilpotent N) (hscale : S * N - N * S = N) :
    Module.End.IsSemisimple (Matrix.toLin' (S - N)) := by
  let D := LieAlgebra.ad F (Matrix (Fin n) (Fin n) F) N
  have hD : IsNilpotent D := LieAlgebra.ad_nilpotent_of_nilpotent hN
  have h₁ : D 1 = 0 := by
    change N * 1 - 1 * N = 0
    simp
  have hder (x y : Matrix (Fin n) (Fin n) F) : D (x * y) = x * D y + D x * y := by
    change N * (x * y) - x * y * N = x * (N * y - y * N) + (N * x - x * N) * y
    noncomm_ring
  let φ := NilpotentDerivationExp.nilpotentDerivationExp D hD h₁ hder
  have hDN : D N = 0 := sub_self _
  have hDS : D S = -N := by
    change N * S - S * N = -N
    calc
      N * S - S * N = -(S * N - N * S) := by abel
      _ = -N := congrArg Neg.neg hscale
  have hφ : φ S = S - N := by
    change IsNilpotent.exp D S = S - N
    rw [NilpotentDerivationExp.nilpotent_exp_apply_of_square_zero D hD S (by rw [hDS, map_neg, hDN, neg_zero]),
      hDS, sub_eq_add_neg]
  exact hφ ▸ matrix_algHom_preserves_semisimple φ S hS

end

end OAI.NumberTheory.Quaternion.Arithmetic.SemisimplePerturbation
