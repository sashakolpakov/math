import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.Elementary
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixSupport

namespace OAI.Algorithms

/-!
# Executable elementary recurrence for the multicolor layout operator

This module connects the list algorithm to the exact operator used by the
support and spectral proofs. The algorithm enumerates positions in Fin Q
directly and never computes a powerset or selects a list from a quotient.
-/

namespace SubexponentialSAT.Subexp.ElementaryMatrix

open SubexponentialSAT.MulticolorTypes
open scoped BigOperators

variable {r Q Δ : ℕ}

/-- A fixed, computable enumeration of all active positions. -/
def activeList (t : Fin Q) : List (Fin Q) :=
  (List.finRange Q).filter (fun l => decide (l ≠ t))

theorem activeList_nodup (t : Fin Q) : (activeList t).Nodup :=
  (List.nodup_finRange Q).filter _

@[simp] theorem activeList_toFinset (t : Fin Q) :
    (activeList t).toFinset = MatrixSupport.activePositions t := by
  ext l
  simp [activeList, MatrixSupport.activePositions, ne_comm]

theorem activeList_length_le (t : Fin Q) : (activeList t).length ≤ Q := by
  simpa [activeList] using
    (List.length_filter_le (fun l : Fin Q => decide (l ≠ t)) (List.finRange Q))

section Operators

variable {K : Type*} [Field K]

/-- The coefficient array computed by the finite recurrence. -/
def operatorCoefficients (i : Fin Δ) (t : Fin Q) (R : ℕ) :
    List (Module.End K (UniversalType r Q Δ → K)) :=
  Elementary.coefficients R
    ((activeList t).map (MatrixSupport.positionProjector i))

@[simp] theorem operatorCoefficients_length (i : Fin Δ) (t : Fin Q) (R : ℕ) :
    (operatorCoefficients (r := r) (K := K) i t R).length = R := by
  simp [operatorCoefficients]

/-- Every retained coefficient is exactly the subset-defined elementary
projector from the mathematical construction. -/
theorem operatorCoefficients_getD (i : Fin Δ) (t : Fin Q) (R j : ℕ)
    (hj : j < R) :
    (operatorCoefficients (r := r) (K := K) i t R).getD j 0 =
      ∑ A ∈ (MatrixSupport.activePositions t).powersetCard j,
        MatrixSupport.projectorLinear i A.toList := by
  unfold operatorCoefficients
  rw [Elementary.coefficients_eq_powersetCard R
    (MatrixSupport.positionProjector i)
    (MatrixSupport.positionProjector_commute i)
    (activeList t) (activeList_nodup t) j hj, activeList_toFinset]
  apply Finset.sum_congr rfl
  intro A _
  exact (MatrixSupport.projectorLinear_eq_list_prod i A.toList).symm

/-- The actual layout operator computed from one shared coefficient array,
without enumerating subsets. -/
def matrixLinearDP (i : Fin Δ) (t : Fin Q) (R : ℕ) (c : ℕ → K) :
    Module.End K (UniversalType r Q Δ → K) :=
  let bs := operatorCoefficients i t R
  MatrixSupport.permutationLinear i (MatrixSupport.activePositions t) *
    ∑ j ∈ Finset.range R, c j • bs.getD j 0

/-- The executable recurrence realizes exactly the operator in equation (3.5). -/
theorem matrixLinearDP_eq (i : Fin Δ) (t : Fin Q) (R : ℕ) (c : ℕ → K) :
    matrixLinearDP (r := r) i t R c = MatrixSupport.matrixLinear i t R c := by
  unfold matrixLinearDP MatrixSupport.matrixLinear
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [operatorCoefficients_getD i t R j (Finset.mem_range.mp hj)]

/-- An executable matrix on the joint fiber, obtained by applying the
computed operator to its actual ambient coordinate vectors. -/
def jointMatrixDP (i : Fin Δ) (t : Fin Q) (g : Fin r) (R : ℕ) (c : ℕ → K) :
    Matrix (Joint t g i) (Joint t g i) K :=
  fun u y => matrixLinearDP i t R c (MatrixSupport.delta y.val) u.val

/-- The executable joint matrix is exactly the one used by the rank and
support theorems. -/
theorem jointMatrixDP_eq (i : Fin Δ) (t : Fin Q) (g : Fin r)
    (R : ℕ) (c : ℕ → K) :
    jointMatrixDP i t g R c = MatrixSupport.jointMatrix i t g R c := by
  ext u y
  simp only [jointMatrixDP, matrixLinearDP_eq, MatrixSupport.jointMatrix]
  exact (MatrixSupport.matrixEntry_eq_matrixLinear i t R c u.val y.val).symm

/-- The matching instrumented coefficient computation uses at most 2 R Q
additions and multiplications of endomorphisms. No bit-cost claim is hidden
in this arithmetic-operation count. -/
theorem operatorCoefficients_operations_le (i : Fin Δ) (t : Fin Q) (R : ℕ) :
    (Elementary.measuredCoefficients R
      ((activeList t).map
        (MatrixSupport.positionProjector (r := r) (K := K) i))).2 ≤ 2 * R * Q := by
  rw [Elementary.measuredCoefficients_operations, List.length_map]
  exact Nat.mul_le_mul_left (2 * R) (activeList_length_le t)

end Operators

end SubexponentialSAT.Subexp.ElementaryMatrix

end OAI.Algorithms
