import OAI.AlgebraicTopology.Cohomology.Singular.CubicalEndpointFaces
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! # Cubical Permutation Signs -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.CubicalPermutationSigns

noncomputable section

/-!
# Cofactor signs for deleting a coordinate from a permutation

The permutation obtained by deleting position p and image σ(p), while retaining
the increasing order on both complements, has the usual cofactor sign. The
proof identifies its actual permutation matrix with the corresponding minor
and applies the determinant expansion along row p.
-/

open _root_.CategoryTheory
open scoped BigOperators

variable {n : ℕ}

/-- The minor obtained by deleting p and σ(p) is precisely the permutation
matrix of the order-preserving deletion used in cubical endpoint faces. -/
theorem eraseCubePermutation_permMatrix (σ : Equiv.Perm (Fin (n + 1)))
    (p : Fin (n + 1)) :
    (σ.permMatrix ℤ).submatrix p.succAbove (σ p).succAbove =
      (CubicalEndpointFaces.eraseCubePermutation σ p).permMatrix ℤ := by
  ext i j
  simp only [Matrix.submatrix_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_some_iff,
    ← CubicalEndpointFaces.eraseCubePermutation_succAbove σ p i, Fin.succAbove_right_inj]

/-- Exact integer cofactor sign for deleting a position and its image. -/
theorem sign_eraseCubePermutation_int (σ : Equiv.Perm (Fin (n + 1)))
    (p : Fin (n + 1)) :
    (Equiv.Perm.sign σ : ℤ) =
      (-1 : ℤ) ^ (p.val + (σ p).val) * (Equiv.Perm.sign (CubicalEndpointFaces.eraseCubePermutation σ p) : ℤ) := by
  calc
    (Equiv.Perm.sign σ : ℤ) = Matrix.det (σ.permMatrix ℤ) :=
      (Matrix.det_permutation σ).symm
    _ = ∑ j : Fin (n + 1), (-1 : ℤ) ^ (p.val + j.val) *
        σ.permMatrix ℤ p j * Matrix.det ((σ.permMatrix ℤ).submatrix p.succAbove j.succAbove) :=
      Matrix.det_succ_row (σ.permMatrix ℤ) p
    _ = _ := by
      rw [Finset.sum_eq_single (σ p)]
      · rw [eraseCubePermutation_permMatrix]
        simp [Equiv.Perm.permMatrix, Equiv.toPEquiv_apply]
      · intro j _ hj
        simp [Equiv.Perm.permMatrix, Equiv.toPEquiv_apply, Ne.symm hj]
      · simp

/-- The cofactor identity also holds in the group of integer units. -/
theorem sign_eraseCubePermutation (σ : Equiv.Perm (Fin (n + 1)))
    (p : Fin (n + 1)) :
    Equiv.Perm.sign σ =
      (-1 : ℤˣ) ^ (p.val + (σ p).val) * Equiv.Perm.sign (CubicalEndpointFaces.eraseCubePermutation σ p) := by
  apply Units.ext
  simpa using sign_eraseCubePermutation_int σ p

/-- The first endpoint has the sign of the upper cube face at direction σ(0). -/
theorem cubePermutation_firstBoundarySign (σ : Equiv.Perm (Fin (n + 1))) :
    (Equiv.Perm.sign σ : ℤ) =
      (-1 : ℤ) ^ (σ 0).val * (Equiv.Perm.sign (CubicalEndpointFaces.eraseCubePermutation σ 0) : ℤ) := by
  simpa using sign_eraseCubePermutation_int σ 0

/-- Including the last simplex boundary sign produces the negative of the
corresponding lower cube-face sign. -/
theorem cubePermutation_lastBoundarySign (σ : Equiv.Perm (Fin (n + 1))) :
    (Equiv.Perm.sign σ : ℤ) * (-1 : ℤ) ^ (n + 1) =
      -((-1 : ℤ) ^ (σ (Fin.last n)).val *
        (Equiv.Perm.sign (CubicalEndpointFaces.eraseCubePermutation σ (Fin.last n)) : ℤ)) := by
  rw [sign_eraseCubePermutation_int σ (Fin.last n), Fin.val_last, pow_add, pow_succ]
  rcases neg_one_pow_eq_or ℤ n with h | h <;> simp [h]

end

end OAI.AlgebraicTopology.Cohomology.Singular.CubicalPermutationSigns
