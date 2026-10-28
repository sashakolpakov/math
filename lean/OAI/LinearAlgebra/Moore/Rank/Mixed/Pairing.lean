import OAI.LinearAlgebra.Moore.Rank.Mixed.Derivative
import OAI.LinearAlgebra.Moore.Rank.Mixed.Cofactor
import OAI.LinearAlgebra.MixedDiscriminant.Polarization

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix

theorem mixedMoore_cons_perm {m : ℕ}
    (P : Matrix (Fin (m + 1)) (Fin (m + 1)) (Quaternion ℝ))
    (A : Fin m → Matrix (Fin (m + 1)) (Fin (m + 1)) (Quaternion ℝ))
    (σ : Equiv.Perm (Fin m)) :
    mixedMoore (m + 1) (Fin.cons P (fun i => A (σ i))) =
      mixedMoore (m + 1) (Fin.cons P A) := by
  have h := mixedMoore_comp_perm (m + 1) (Fin.cons P A)
    (Equiv.Perm.decomposeFin.symm (0, σ))
  convert h using 1
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ i => simp

theorem realTrace_finset_sum {ι : Type*} {m : ℕ} (S : Finset ι)
    (A : ι → Matrix (Fin m) (Fin m) (Quaternion ℝ)) :
    realTrace (∑ i ∈ S, A i) = ∑ i ∈ S, realTrace (A i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [realTrace]
  | @insert a S ha ih => simp only [Finset.sum_insert ha, realTrace_add, ih]

/-- The mixed cofactor has the ordinary real-trace normalization: its
pairing with a Hermitian matrix is the degree times the mixed determinant. -/
theorem mixedCofactor_pairing {m : ℕ}
    (A : Fin m → Matrix (Fin (m + 1)) (Fin (m + 1)) (Quaternion ℝ))
    (P : Matrix (Fin (m + 1)) (Fin (m + 1)) (Quaternion ℝ)) (hP : P.IsHermitian) :
    realTrace (mixedCofactor (m + 1) A * P) =
      (m + 1 : ℝ) * mixedMoore (m + 1) (Fin.cons P A) := by
  have hp := OAI.LinearAlgebra.MixedDiscriminant.symmetric_multilinear_polarization
    ((mixedMoore (m + 1)).curryLeft P) (mixedMoore_cons_perm P) A
  simp only [MultilinearMap.curryLeft_apply] at hp
  rw [mixedCofactor_eq_sum, Matrix.smul_mul, realTrace_smul, Finset.sum_mul,
    realTrace_finset_sum]
  simp only [Nat.add_sub_cancel, Matrix.smul_mul, realTrace_smul,
    mooreCofactor_pairing _ _ P hP, mooreDifferential_eq_mixedMoore]
  rw [← hp]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  ring_nf
  congr 1

theorem mixedCofactor_isHermitian (m : ℕ)
    (A : Fin (m - 1) → Matrix (Fin m) (Fin m) (Quaternion ℝ)) :
    (mixedCofactor m A).IsHermitian := by
  classical
  rw [Matrix.IsHermitian, mixedCofactor_eq_sum,
    quaternionMatrix_conjTranspose_real_smul, Matrix.conjTranspose_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro S hS
  rw [quaternionMatrix_conjTranspose_real_smul, mooreCofactor_isHermitian]

end OAI.LinearAlgebra.Moore
