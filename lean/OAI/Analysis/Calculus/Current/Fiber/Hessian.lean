import OAI.Analysis.Calculus.Current.Fiber.Kernel
import OAI.Analysis.Calculus.Quaternion.Gram

namespace OAI.Analysis.Calculus.Current

noncomputable section
open scoped Matrix

theorem contDiffAt_fiberMap_complex {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) (i : Option (Fin d)) :
    ContDiffAt ℂ 2 (fun q => fiberMap w a q i) z := by
  cases i <;> unfold fiberMap phi ratio <;>
    fun_prop (disch := exact mul_ne_zero (two_ne_zero : (2 : ℂ) ≠ 0) hY)

theorem fderiv_fiberMap {d : ℕ} (w a : ℝ) (z h : Index d → ℂ)
    (hY : z none ≠ 0) (i : Option (Fin d)) :
    fderiv ℂ (fun q => fiberMap w a q i) z h = (fiberJacobian w a z *ᵥ h) i := by
  have hf := (contDiffAt_fiberMap_complex w a z hY i).differentiableAt (by norm_num)
  have hl : HasDerivAt (fun t : ℂ => fun b => z b + t * h b) h 0 := by
    convert ((hasDerivAt_id (0 : ℂ)).smul_const h).const_add z using 1
    · funext t b
      simp
    · simp
  have hf' : HasFDerivAt (fun q => fiberMap w a q i)
      (fderiv ℂ (fun q => fiberMap w a q i) z) (fun b => z b + (0 : ℂ) * h b) := by
    simpa only [zero_mul, add_zero] using hf.hasFDerivAt
  have hh := hf'.comp_hasDerivAt 0 hl
  exact hh.unique (hasDerivAt_fiberMap_complexLine w a z h hY i)

theorem fderiv_fiberMap_single {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) (i : Option (Fin d)) (b : Index d) :
    fderiv ℂ (fun q => fiberMap w a q i) z (Pi.single b 1) = fiberJacobian w a z i b := by
  rw [fderiv_fiberMap w a z _ hY i]
  simp only [Matrix.mulVec_single_one]
  rfl

def quaternionFiberJacobian {d : ℕ} (w a : ℝ) (z : Index d → ℂ) :
    Matrix (Option (Fin d)) (Index d) (Quaternion ℝ) :=
  fun i b => complexK (fiberJacobian w a z i b)

def fiberHessian {d : ℕ} (w a : ℝ) (z : Index d → ℂ) :
    Matrix (Index d) (Index d) (Quaternion ℝ) :=
  OAI.Analysis.Calculus.Quaternion.imaginaryHessian (fiberDefining w a) z

/-- The actual fiber Hessian is four times the Gram matrix of its holomorphic Jacobian. -/
theorem fiberHessian_factorization {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) :
    fiberHessian w a z =
      (4 : ℝ) • ((quaternionFiberJacobian w a z)ᴴ * quaternionFiberJacobian w a z) := by
  unfold fiberHessian fiberDefining
  rw [OAI.Analysis.Calculus.Quaternion.imaginaryHessian_sub_const]
  have hh := OAI.Analysis.Calculus.Quaternion.imaginaryHessian_holomorphic_squares (fun i q => fiberMap w a q i)
    (fun i => contDiffAt_fiberMap_complex w a z hY i)
  simp only [fderiv_fiberMap_single w a z hY] at hh
  exact hh

theorem quaternionFiberJacobian_kernel {d : ℕ} (w a : ℝ) (z : Index d → ℂ) :
    quaternionFiberJacobian w a z *ᵥ (fun b => complexK (fiberKernelVector z b)) = 0 := by
  funext i
  have h := congrFun (fiberJacobian_kernel w a z) i
  have hh := congrArg complexK h
  simpa only [Matrix.mulVec, dotProduct, map_sum, map_mul, map_zero,
    quaternionFiberJacobian, Pi.zero_apply] using hh

theorem fiberHessian_kernel {d : ℕ} (w a : ℝ) (z : Index d → ℂ) (hY : z none ≠ 0) :
    fiberHessian w a z *ᵥ (fun b => complexK (fiberKernelVector z b)) = 0 := by
  rw [fiberHessian_factorization w a z hY, Matrix.smul_mulVec,
    ← Matrix.mulVec_mulVec, quaternionFiberJacobian_kernel, Matrix.mulVec_zero, smul_zero]

theorem fiberHessian_nonneg {d : ℕ} (w a : ℝ) (z : Index d → ℂ) (hY : z none ≠ 0)
    (v : Index d → Quaternion ℝ) : 0 ≤ (star v ⬝ᵥ (fiberHessian w a z *ᵥ v)).re := by
  rw [fiberHessian_factorization w a z hY, Matrix.smul_mulVec, dotProduct_smul]
  simpa only [Quaternion.re_smul, smul_eq_mul] using
    mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      (OAI.Analysis.Calculus.Quaternion.quaternionGram_nonneg (quaternionFiberJacobian w a z) v)

end
end OAI.Analysis.Calculus.Current
