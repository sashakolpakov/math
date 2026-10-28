import OAI.Analysis.Calculus.Current.Fiber.Hessian

namespace OAI.Analysis.Calculus.Current

noncomputable section
open scoped Matrix

def quaternionFirst : Quaternion ℝ →+ ℂ where
  toFun q := ⟨q.re, q.imK⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def quaternionSecond : Quaternion ℝ →+ ℂ where
  toFun q := ⟨q.imI, q.imJ⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem quaternionFirst_complexK_mul (c : ℂ) (q : Quaternion ℝ) :
    quaternionFirst (complexK c * q) = c * quaternionFirst q := by
  apply Complex.ext <;> simp [quaternionFirst, complexK]

theorem quaternionSecond_complexK_mul (c : ℂ) (q : Quaternion ℝ) :
    quaternionSecond (complexK c * q) = c * quaternionSecond q := by
  apply Complex.ext <;> simp [quaternionSecond, complexK]

theorem quaternion_eq_of_components {q r : Quaternion ℝ}
    (h₁ : quaternionFirst q = quaternionFirst r)
    (h₂ : quaternionSecond q = quaternionSecond r) : q = r := by
  apply Quaternion.ext
  · exact congrArg Complex.re h₁
  · exact congrArg Complex.re h₂
  · exact congrArg Complex.im h₂
  · exact congrArg Complex.im h₁

theorem fiberJacobian_first_of_quaternion_kernel {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (v : Index d → Quaternion ℝ) (hJ : quaternionFiberJacobian w a z *ᵥ v = 0) :
    fiberJacobian w a z *ᵥ (fun b => quaternionFirst (v b)) = 0 := by
  funext i
  have h := congrArg quaternionFirst (congrFun hJ i)
  simpa only [Matrix.mulVec, dotProduct, quaternionFiberJacobian, map_sum,
    quaternionFirst_complexK_mul, Pi.zero_apply, map_zero] using h

theorem fiberJacobian_second_of_quaternion_kernel {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (v : Index d → Quaternion ℝ) (hJ : quaternionFiberJacobian w a z *ᵥ v = 0) :
    fiberJacobian w a z *ᵥ (fun b => quaternionSecond (v b)) = 0 := by
  funext i
  have h := congrArg quaternionSecond (congrFun hJ i)
  simpa only [Matrix.mulVec, dotProduct, quaternionFiberJacobian, map_sum,
    quaternionSecond_complexK_mul, Pi.zero_apply, map_zero] using h

/-- The complex one-dimensional kernel is also one-dimensional over the quaternions. -/
theorem quaternionFiberJacobian_kernel_unique {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (v : Index d → Quaternion ℝ) (hw : w ≠ 0) (ha : a ≠ 0) (hY : z none ≠ 0)
    (hJ : quaternionFiberJacobian w a z *ᵥ v = 0) :
    v = fun b => complexK (fiberKernelVector z b) * v none := by
  have h₁ := fiberJacobian_kernel_unique w a z _ hw ha hY
    (fiberJacobian_first_of_quaternion_kernel w a z v hJ)
  have h₂ := fiberJacobian_kernel_unique w a z _ hw ha hY
    (fiberJacobian_second_of_quaternion_kernel w a z v hJ)
  funext b
  apply quaternion_eq_of_components
  · rw [quaternionFirst_complexK_mul]
    exact congrFun h₁ b
  · rw [quaternionSecond_complexK_mul]
    exact congrFun h₂ b

theorem quaternionFiberJacobian_spatial_injective {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (v : Index d → Quaternion ℝ) (hw : w ≠ 0) (ha : a ≠ 0) (hY : z none ≠ 0)
    (hD : fiberDenominator (ratio z) ≠ 0) (htime : v none = v (some none))
    (hJ : quaternionFiberJacobian w a z *ᵥ v = 0) : v = 0 := by
  have h₁ := fiberJacobian_spatial_injective w a z _ hw ha hY hD
    (congrArg quaternionFirst htime) (fiberJacobian_first_of_quaternion_kernel w a z v hJ)
  have h₂ := fiberJacobian_spatial_injective w a z _ hw ha hY hD
    (congrArg quaternionSecond htime) (fiberJacobian_second_of_quaternion_kernel w a z v hJ)
  funext b
  apply quaternion_eq_of_components
  · exact congrFun h₁ b
  · exact congrFun h₂ b

/-- Positive definiteness on every fixed-physical-time tangent space. -/
theorem fiberHessian_spatial_pos {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (v : Index d → Quaternion ℝ) (hw : w ≠ 0) (ha : a ≠ 0) (hY : z none ≠ 0)
    (hD : fiberDenominator (ratio z) ≠ 0) (htime : v none = v (some none)) (hv : v ≠ 0) :
    0 < (star v ⬝ᵥ (fiberHessian w a z *ᵥ v)).re := by
  have hJ : quaternionFiberJacobian w a z *ᵥ v ≠ 0 := by
    intro h
    exact hv (quaternionFiberJacobian_spatial_injective w a z v hw ha hY hD htime h)
  rw [fiberHessian_factorization w a z hY, Matrix.smul_mulVec, dotProduct_smul]
  simpa only [Quaternion.re_smul, smul_eq_mul] using
    mul_pos (by norm_num : (0 : ℝ) < 4)
      (OAI.Analysis.Calculus.Quaternion.quaternionGram_pos (quaternionFiberJacobian w a z) v hJ)

theorem fiberHessian_kernel_iff {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) (v : Index d → Quaternion ℝ) :
    fiberHessian w a z *ᵥ v = 0 ↔ quaternionFiberJacobian w a z *ᵥ v = 0 := by
  rw [fiberHessian_factorization w a z hY, Matrix.smul_mulVec]
  rw [smul_eq_zero_iff_right (by norm_num : (4 : ℝ) ≠ 0)]
  exact OAI.Analysis.Calculus.Quaternion.quaternionGram_kernel _ _

/-- The full Hessian has exactly the displayed one-dimensional right quaternionic kernel. -/
theorem fiberHessian_kernel_unique {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (v : Index d → Quaternion ℝ) (hw : w ≠ 0) (ha : a ≠ 0) (hY : z none ≠ 0)
    (hH : fiberHessian w a z *ᵥ v = 0) :
    v = fun b => complexK (fiberKernelVector z b) * v none :=
  quaternionFiberJacobian_kernel_unique w a z v hw ha hY
    ((fiberHessian_kernel_iff w a z hY v).mp hH)

theorem fiberHessian_spatial_pos_on_fiber {d : ℕ} (a : ℝ) (z : Index d → ℂ)
    (v : Index d → Quaternion ℝ) (ha : a ≠ 0) (hY : z none ≠ 0)
    (hr : fiberDefining (1 / 10) a z ≤ 0) (htime : v none = v (some none)) (hv : v ≠ 0) :
    0 < (star v ⬝ᵥ (fiberHessian (1 / 10) a z *ᵥ v)).re :=
  fiberHessian_spatial_pos (1 / 10) a z v (by norm_num) ha hY
    (fiberDenominator_ne_zero_on_fiber a z hr) htime hv

end
end OAI.Analysis.Calculus.Current
