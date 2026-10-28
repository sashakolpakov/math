import OAI.Analysis.PDE.Dirichlet.Covariance

namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion Matrix
open scoped Matrix

/-- Apply one real change of variable index identically to every slot. -/
noncomputable def slotLift {n s : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ :=
  fun p q => if p.2 = q.2 then R p.1 q.1 else 0

theorem slotLift_mul_starSlot {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (R : Matrix (Fin n) (Fin n) ℝ) :
    OAI.Analysis.PDE.Dirichlet.realLift (slotLift (s := s) R) * (OAI.Analysis.PDE.Dirichlet.slotMatrix n s e)ᴴ =
      (OAI.Analysis.PDE.Dirichlet.slotMatrix n s e)ᴴ * OAI.Analysis.PDE.Dirichlet.realLift R := by
  classical
  apply Matrix.ext
  intro p b
  rcases p with ⟨a, α⟩
  simp [Matrix.mul_apply, Fintype.sum_prod_type, slotLift, OAI.Analysis.PDE.Dirichlet.slotMatrix,
    Matrix.conjTranspose_apply, OAI.Analysis.PDE.Dirichlet.realLift_apply, apply_ite, ite_mul]

theorem hessianMap_mul_slotLift {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (H : Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ)
    (R : Matrix (Fin n) (Fin n) ℝ) :
    OAI.Analysis.Calculus.Quaternion.hessianMap e (H * slotLift R) = OAI.Analysis.Calculus.Quaternion.hessianMap e H * OAI.Analysis.PDE.Dirichlet.realLift R := by
  rw [OAI.Analysis.PDE.Dirichlet.hessianMap_eq_slotMatrix, OAI.Analysis.PDE.Dirichlet.hessianMap_eq_slotMatrix]
  rw [OAI.Analysis.PDE.Dirichlet.realLift_mul, Matrix.mul_assoc, Matrix.mul_assoc, slotLift_mul_starSlot]
  simp only [Matrix.mul_assoc]

/-- Quaternionic Hessian covariance for real index changes. This algebraic
identity does not require orthogonality, positivity, or invertibility. -/
theorem hessianMap_slotLift_congruence {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (H : Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ)
    (R : Matrix (Fin n) (Fin n) ℝ) :
    OAI.Analysis.Calculus.Quaternion.hessianMap e ((slotLift R)ᵀ * H * slotLift R) =
      (OAI.Analysis.PDE.Dirichlet.realLift R)ᴴ * OAI.Analysis.Calculus.Quaternion.hessianMap e H * OAI.Analysis.PDE.Dirichlet.realLift R := by
  rw [hessianMap_mul_slotLift]
  have he : (slotLift (s := s) R)ᵀ * H = (Hᵀ * slotLift R)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  rw [he, OAI.Analysis.PDE.Dirichlet.hessianMap_transpose, hessianMap_mul_slotLift, Matrix.conjTranspose_mul,
    OAI.Analysis.PDE.Dirichlet.hessianMap_transpose, Matrix.conjTranspose_conjTranspose]

theorem realMatrixAction_coordinateVector {n s : ℕ}
    (Q : Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ) (i j : Fin n × Fin s) :
    OAI.Analysis.PDE.Dirichlet.realMatrixAction Q (OAI.Analysis.PDE.Dirichlet.coordinateVector j) i = Q i j := by
  simp [OAI.Analysis.PDE.Dirichlet.realMatrixAction, OAI.Analysis.PDE.Dirichlet.coordinateVector, Matrix.mulVec, dotProduct]

theorem realHessian_linear_comp {n s : ℕ} {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ}
    (hf : ContDiff ℝ 2 f) (Q : Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
    OAI.Analysis.PDE.Dirichlet.realHessian (f ∘ OAI.Analysis.PDE.Dirichlet.realMatrixAction Q) x = Qᵀ * OAI.Analysis.PDE.Dirichlet.realHessian f (OAI.Analysis.PDE.Dirichlet.realMatrixAction Q x) * Q := by
  apply Matrix.ext
  intro i j
  have hd := congrArg (fun T => T ![OAI.Analysis.PDE.Dirichlet.coordinateVector i, OAI.Analysis.PDE.Dirichlet.coordinateVector j])
    ((OAI.Analysis.PDE.Dirichlet.realMatrixAction Q).iteratedFDeriv_comp_right hf x (i := 2) le_rfl)
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hd
  change (fderiv ℝ (fderiv ℝ (f ∘ OAI.Analysis.PDE.Dirichlet.realMatrixAction Q)) x (OAI.Analysis.PDE.Dirichlet.coordinateVector i))
    (OAI.Analysis.PDE.Dirichlet.coordinateVector j) = _
  rw [hd, ← OAI.Analysis.PDE.Dirichlet.realHessian_bilinear]
  simp only [realMatrixAction_coordinateVector, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Covariance of the actual differentiated quaternionic Hessian under a
real index change applied in every slot. -/
theorem quaternionHessian_slot_comp {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hf : ContDiff ℝ 2 f)
    (R : Matrix (Fin n) (Fin n) ℝ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
    OAI.Analysis.PDE.Dirichlet.quaternionHessian e (f ∘ OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift R)) x =
      (OAI.Analysis.PDE.Dirichlet.realLift R)ᴴ * OAI.Analysis.PDE.Dirichlet.quaternionHessian e f (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift R) x) * OAI.Analysis.PDE.Dirichlet.realLift R := by
  unfold OAI.Analysis.PDE.Dirichlet.quaternionHessian
  rw [realHessian_linear_comp hf, hessianMap_slotLift_congruence]

end OAI.Analysis.PDE.Concentration
