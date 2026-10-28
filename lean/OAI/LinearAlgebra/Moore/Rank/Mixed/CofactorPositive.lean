import OAI.LinearAlgebra.Moore.Rank.Mixed.Positive
import OAI.LinearAlgebra.Moore.Rank.Mixed.Pairing
import OAI.LinearAlgebra.Moore.Adjugate

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open scoped ComplexOrder

/-- The actual mixed cofactor is positive semidefinite on PSD arguments. -/
theorem mixedCofactor_posSemidef (m : ℕ)
    (A : Fin (m - 1) → Matrix (Fin m) (Fin m) (Quaternion ℝ))
    (hA : ∀ i, (complexify (A i)).PosSemidef) :
    (complexify (mixedCofactor m A)).PosSemidef := by
  apply (complexify_posSemidef_iff (mixedCofactor_isHermitian m A)).mpr
  intro z
  cases m with
  | zero => simp [OAI.Analysis.PDE.Dirichlet.quaternionForm]
  | succ m =>
    rw [← realTrace_mul_outer, mixedCofactor_pairing (m := m) A (OAI.Analysis.Calculus.Quaternion.outer z)
      (OAI.Analysis.Calculus.Quaternion.outer_isHermitian z)]
    apply mul_nonneg (by positivity)
    apply mixedMoore_nonneg
    intro i
    cases i using Fin.cases with
    | zero => exact complexify_outer_posSemidef z
    | succ i => exact hA i

/-- Hermitian matrices are determined by their real-trace pairings with
Hermitian test matrices. -/
theorem eq_of_realTrace_mul_eq_hermitian {m : ℕ}
    (A B : Matrix (Fin m) (Fin m) (Quaternion ℝ))
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : ∀ P, P.IsHermitian → realTrace (A * P) = realTrace (B * P)) : A = B := by
  apply sub_eq_zero.mp
  apply eq_zero_of_realTrace_mul_eq_zero
  intro P
  have hP : (P + Pᴴ).IsHermitian := by
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, add_comm]
  have hstar (C : Matrix (Fin m) (Fin m) (Quaternion ℝ)) (hC : C.IsHermitian) :
      realTrace (C * Pᴴ) = realTrace (C * P) := by
    rw [realTrace_mul_comm C Pᴴ, realTrace_star_left P C hC, realTrace_mul_comm P C]
  have he := h (P + Pᴴ) hP
  simp only [Matrix.mul_add, realTrace_add, hstar A hA, hstar B hB] at he
  rw [Matrix.sub_mul, realTrace_sub]
  linarith

/-- Repeating the same argument recovers the ordinary Moore cofactor. -/
theorem mixedCofactor_const (m : ℕ)
    (A : Matrix (Fin m) (Fin m) (Quaternion ℝ)) :
    mixedCofactor m (fun _ => A) = mooreCofactor m A := by
  cases m with
  | zero => exact Subsingleton.elim _ _
  | succ m =>
    apply eq_of_realTrace_mul_eq_hermitian _ _
      (mixedCofactor_isHermitian _ _) (mooreCofactor_isHermitian _ _)
    intro P hP
    rw [mixedCofactor_pairing _ P hP, mooreCofactor_pairing _ A P hP,
      mooreDifferential_eq_mixedMoore]
    congr 1

end OAI.LinearAlgebra.Moore
