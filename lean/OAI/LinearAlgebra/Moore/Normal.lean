import OAI.LinearAlgebra.Moore.Adjugate

/-! Vanishing of the normal cofactor from a singular tangential restriction.
The full Hermitian matrix is allowed to be indefinite. -/

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion

theorem mulVec_right_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (v : Fin n → Quaternion ℝ) (q : Quaternion ℝ) :
    A *ᵥ (fun i ↦ v i * q) = fun i ↦ (A *ᵥ v) i * q := by
  funext i
  simp only [Matrix.mulVec, dotProduct, mul_assoc, Finset.sum_mul]

theorem dotProduct_right_mul {n : ℕ} (u v : Fin n → Quaternion ℝ)
    (q : Quaternion ℝ) :
    u ⬝ᵥ (fun i ↦ v i * q) = (u ⬝ᵥ v) * q := by
  simp only [dotProduct, Finset.sum_mul, mul_assoc]

theorem outer_mulVec_orthogonal {n : ℕ} (ν v : Fin n → Quaternion ℝ)
    (hv : star ν ⬝ᵥ v = 0) : OAI.Analysis.Calculus.Quaternion.outer ν *ᵥ v = 0 := by
  funext i
  change (∑ j, (ν i * star (ν j)) * v j) = 0
  simp only [mul_assoc, ← Finset.mul_sum]
  change ν i * (star ν ⬝ᵥ v) = 0
  rw [hv, mul_zero]

theorem mooreCofactor_normal_zero_of_kernel {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hA : A.IsHermitian)
    (ν v : Fin n → Quaternion ℝ) (hv : v ≠ 0)
    (hAv : A *ᵥ v = 0) (horth : star ν ⬝ᵥ v = 0) :
    (OAI.Analysis.PDE.Dirichlet.quaternionForm (mooreCofactor n A) ν).re = 0 := by
  have hzero (t : ℝ) : mooreDet n (A + t • OAI.Analysis.Calculus.Quaternion.outer ν) = 0 := by
    apply mooreDet_zero_of_kernel n _ _ v _ hv
    · change (A + t • OAI.Analysis.Calculus.Quaternion.outer ν)ᴴ = A + t • OAI.Analysis.Calculus.Quaternion.outer ν
      rw [Matrix.conjTranspose_add, quaternionMatrix_conjTranspose_real_smul,
        hA, OAI.Analysis.Calculus.Quaternion.outer_isHermitian]
    · simp only [Matrix.add_mulVec, Matrix.smul_mulVec, hAv,
        outer_mulVec_orthogonal ν v horth, smul_zero, add_zero]
  have hd := hasDerivAt_mooreDet_affine A (OAI.Analysis.Calculus.Quaternion.outer ν) 0
  have hc : HasDerivAt (fun t : ℝ ↦ mooreDet n (A + t • OAI.Analysis.Calculus.Quaternion.outer ν)) 0 0 := by
    simpa only [hzero] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
  have he := hd.unique hc
  simp only [zero_smul, add_zero] at he
  rw [← mooreCofactor_pairing n A (OAI.Analysis.Calculus.Quaternion.outer ν) (OAI.Analysis.Calculus.Quaternion.outer_isHermitian ν),
    realTrace_mul_outer] at he
  exact he

/-- If the restriction of `A` to the normal orthogonal complement has a
nonzero null vector, its normal cofactor vanishes. No positivity is needed. -/
theorem mooreCofactor_normal_zero_of_tangential_kernel {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hA : A.IsHermitian)
    (ν v : Fin n → Quaternion ℝ) (hv : v ≠ 0)
    (horth : star ν ⬝ᵥ v = 0) (q : Quaternion ℝ)
    (hAv : A *ᵥ v = fun i ↦ ν i * q) :
    (OAI.Analysis.PDE.Dirichlet.quaternionForm (mooreCofactor n A) ν).re = 0 := by
  by_cases hq : q = 0
  · apply mooreCofactor_normal_zero_of_kernel A hA ν v hv _ horth
    simpa only [hq, mul_zero, Pi.zero_def] using hAv
  · have hCV : (fun i ↦ (mooreCofactor n A *ᵥ ν) i * q) = mooreDet n A • v := by
      rw [← mulVec_right_mul, ← hAv, Matrix.mulVec_mulVec, mooreCofactor_mul A hA]
      simp only [Matrix.smul_mulVec, Matrix.one_mulVec]
    have hd := congrArg (fun w ↦ star ν ⬝ᵥ w) hCV
    rw [dotProduct_right_mul] at hd
    have hr : star ν ⬝ᵥ (mooreDet n A • v) = 0 := by
      change (∑ i, star (ν i) * (mooreDet n A • v i)) = 0
      simp only [mul_smul_comm, ← Finset.smul_sum]
      change mooreDet n A • (star ν ⬝ᵥ v) = 0
      rw [horth, smul_zero]
    rw [hr, ← quaternionForm_eq_dotProduct] at hd
    have hz := (mul_eq_zero.mp hd).resolve_right hq
    rw [hz]
    rfl

end OAI.LinearAlgebra.Moore
