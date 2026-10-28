import OAI.LinearAlgebra.Moore.Cofactor
import OAI.LinearAlgebra.Moore.Kernel

/-! The cofactor adjugate identity, including singular quaternionic matrices. -/

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix

theorem realTrace_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    realTrace (A - B) = realTrace A - realTrace B := by simp [realTrace]

theorem realTrace_mul_single {n : ℕ} (C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (i j : Fin n) (q : Quaternion ℝ) :
    realTrace (C * Matrix.single i j q) = (C j i * q).re := by
  change (∑ k, ∑ l, C k l * Matrix.single i j q l k).re = (C j i * q).re
  simp [Matrix.single, ite_and, mul_ite]

theorem eq_zero_of_realTrace_mul_eq_zero {n : ℕ}
    (C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (h : ∀ D, realTrace (C * D) = 0) : C = 0 := by
  apply Matrix.ext
  intro i j
  have he := h (Matrix.single j i (star (C i j)))
  rw [realTrace_mul_single, Quaternion.self_mul_star] at he
  exact Quaternion.normSq_eq_zero.mp he

theorem realTrace_symmetric_variation {n : ℕ}
    (A C E : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : A.IsHermitian) (hC : C.IsHermitian) :
    realTrace (C * (E * A + A * Eᴴ)) = 2 * realTrace (A * C * E) := by
  have hAe : Aᴴ = A := hA
  have hCe : Cᴴ = C := hC
  have hfirst : realTrace (C * E * A) = realTrace (A * C * E) := by
    rw [realTrace_mul_comm (C * E) A, Matrix.mul_assoc]
  have hsecond : realTrace (C * A * Eᴴ) = realTrace (A * C * E) := by
    calc
      realTrace (C * A * Eᴴ) = realTrace (E * A * C)ᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hAe, hCe, Matrix.mul_assoc]
      _ = realTrace (E * A * C) := realTrace_conjTranspose _
      _ = realTrace (A * C * E) := by
        rw [Matrix.mul_assoc, realTrace_mul_comm E (A * C)]
  rw [Matrix.mul_add, realTrace_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    hfirst, hsecond]
  ring

/-- Quaternionic adjugate identity derived from congruence variation, with no
invertibility hypothesis. -/
theorem mul_mooreCofactor {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hA : A.IsHermitian) :
    A * mooreCofactor n A = mooreDet n A • (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_realTrace_mul_eq_zero
  intro E
  have hAe : Aᴴ = A := hA
  have hvar : (E * A + A * Eᴴ).IsHermitian := by
    simp only [Matrix.IsHermitian, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hAe, add_comm]
  have h := mooreDifferential_congruence n A E
  rw [← mooreCofactor_pairing n A _ hvar,
    realTrace_symmetric_variation A _ E hA (mooreCofactor_isHermitian n A),
    complexify_trace_real] at h
  have ht : (∑ i, (E i i).re) = realTrace E := by
    change (∑ i, (E i i).re) = (∑ i, E i i).re
    rw [quaternion_re_sum]
  rw [ht] at h
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, realTrace_sub, realTrace_smul]
  linarith

theorem mooreCofactor_mul {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hA : A.IsHermitian) :
    mooreCofactor n A * A = mooreDet n A • (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)) := by
  have h := congrArg Matrix.conjTranspose (mul_mooreCofactor A hA)
  have hAe : Aᴴ = A := hA
  have hCe : (mooreCofactor n A)ᴴ = mooreCofactor n A := mooreCofactor_isHermitian n A
  simpa only [Matrix.conjTranspose_mul, hAe, hCe, quaternionMatrix_conjTranspose_real_smul,
    Matrix.conjTranspose_one] using h

theorem mooreCofactor_image_in_kernel {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hA : A.IsHermitian)
    (hdet : mooreDet n A = 0) (z : Fin n → Quaternion ℝ) :
    A *ᵥ (mooreCofactor n A *ᵥ z) = 0 := by
  rw [Matrix.mulVec_mulVec, mul_mooreCofactor A hA, hdet, zero_smul, Matrix.zero_mulVec]

end OAI.LinearAlgebra.Moore
