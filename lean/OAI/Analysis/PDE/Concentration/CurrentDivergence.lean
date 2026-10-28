import OAI.Analysis.PDE.Concentration.CurrentCovariance

namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion Matrix
open scoped Matrix

theorem realLift_orthogonal {n : ℕ} {R : Matrix (Fin n) (Fin n) ℝ}
    (hR : R * Rᵀ = 1) : OAI.Analysis.PDE.Dirichlet.realLift R * (OAI.Analysis.PDE.Dirichlet.realLift R)ᴴ = 1 := by
  rw [← OAI.Analysis.PDE.Dirichlet.realLift_transpose, ← OAI.Analysis.PDE.Dirichlet.realLift_mul, hR]
  apply Matrix.ext
  intro i j
  simp [OAI.Analysis.PDE.Dirichlet.realLift, Matrix.one_apply, apply_ite]

theorem orthogonal_conjugate_row_sum {n : ℕ} {R : Matrix (Fin n) (Fin n) ℝ}
    (hR : R * Rᵀ = 1) (M : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (c b : Fin n) :
    (∑ a, R c a • ((OAI.Analysis.PDE.Dirichlet.realLift R)ᴴ * M * OAI.Analysis.PDE.Dirichlet.realLift R) a b) = (M * OAI.Analysis.PDE.Dirichlet.realLift R) c b := by
  have h : OAI.Analysis.PDE.Dirichlet.realLift R * ((OAI.Analysis.PDE.Dirichlet.realLift R)ᴴ * M * OAI.Analysis.PDE.Dirichlet.realLift R) = M * OAI.Analysis.PDE.Dirichlet.realLift R := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, realLift_orthogonal hR, Matrix.one_mul]
  have he := congrFun (congrFun h c) b
  simpa only [Matrix.mul_apply, OAI.Analysis.PDE.Dirichlet.realLift_apply, smul_mul_assoc, one_mul] using he

/-- The derivative tensor obtained by rotating both the independent
variables and the two matrix indices. -/
noncomputable def rotatedCurrentDerivative {n s : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    (dA : Fin n × Fin s → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (p : Fin n × Fin s) : Matrix (Fin n) (Fin n) (Quaternion ℝ) :=
  ∑ c, R c p.1 • ((OAI.Analysis.PDE.Dirichlet.realLift R)ᴴ * dA (c, p.2) * OAI.Analysis.PDE.Dirichlet.realLift R)

/-- Strong quaternionic divergence is covariant under real orthogonal
changes of the variable index, applied identically in every real slot. -/
theorem strongDivergence_rotatedCurrentDerivative {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {R : Matrix (Fin n) (Fin n) ℝ} (hR : R * Rᵀ = 1)
    (dA : Fin n × Fin s → Matrix (Fin n) (Fin n) (Quaternion ℝ)) (b : Fin n) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence e (rotatedCurrentDerivative R dA) b =
      ∑ j, OAI.Analysis.Calculus.Quaternion.strongDivergence e dA j * OAI.Analysis.PDE.Dirichlet.realLift R j b := by
  classical
  unfold OAI.Analysis.Calculus.Quaternion.strongDivergence rotatedCurrentDerivative
  simp only [Matrix.sum_apply, Matrix.smul_apply, Finset.mul_sum]
  calc
    (∑ a, ∑ α, ∑ c, star (e α) *
      (R c a • ((OAI.Analysis.PDE.Dirichlet.realLift R)ᴴ * dA (c, α) * OAI.Analysis.PDE.Dirichlet.realLift R) a b)) =
      ∑ α, ∑ c, star (e α) *
        (∑ a, R c a • ((OAI.Analysis.PDE.Dirichlet.realLift R)ᴴ * dA (c, α) * OAI.Analysis.PDE.Dirichlet.realLift R) a b) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro α hα
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
    _ = ∑ α, ∑ c, star (e α) * (dA (c, α) * OAI.Analysis.PDE.Dirichlet.realLift R) c b := by
      simp_rw [orthogonal_conjugate_row_sum hR]
    _ = ∑ j, (∑ a, ∑ α, star (e α) * dA (a, α) a j) * OAI.Analysis.PDE.Dirichlet.realLift R j b := by
      simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      conv_lhs =>
        rw [Finset.sum_comm]
        arg 2
        ext c
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]

theorem strongDivergence_rotatedCurrentDerivative_zero {n s : ℕ}
    (e : Fin s → Quaternion ℝ) {R : Matrix (Fin n) (Fin n) ℝ} (hR : R * Rᵀ = 1)
    (dA : Fin n × Fin s → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hdiv : ∀ b, OAI.Analysis.Calculus.Quaternion.strongDivergence e dA b = 0) (b : Fin n) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence e (rotatedCurrentDerivative R dA) b = 0 := by
  rw [strongDivergence_rotatedCurrentDerivative e hR]
  simp_rw [hdiv]
  simp

end OAI.Analysis.PDE.Concentration
