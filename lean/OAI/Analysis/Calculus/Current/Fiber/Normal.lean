import OAI.Analysis.Calculus.Current.Fiber.Quaternion

namespace OAI.Analysis.Calculus.Current

noncomputable section
open scoped Matrix

def fiberGradient {d : ℕ} (w a : ℝ) (z : Index d → ℂ) : Index d → Quaternion ℝ :=
  OAI.Analysis.Calculus.Quaternion.imaginaryGradient (fiberDefining w a) z

theorem fiberGradient_formula {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) (b : Index d) :
    fiberGradient w a z b = (2 : ℝ) •
      (((quaternionFiberJacobian w a z)ᴴ *ᵥ (fun i => complexK (fiberMap w a z i))) b * qi) := by
  unfold fiberGradient fiberDefining
  rw [OAI.Analysis.Calculus.Quaternion.imaginaryGradient_sub_const, OAI.Analysis.Calculus.Quaternion.imaginaryGradient_sum _ (fun i =>
    ((contDiffAt_fiberMap_complex w a z hY i).differentiableAt (by norm_num)).restrictScalars ℝ |>.norm_sq ℂ)]
  simp_rw [OAI.Analysis.Calculus.Quaternion.imaginaryGradient_norm_sq
    ((contDiffAt_fiberMap_complex w a z hY _).differentiableAt (by norm_num)),
    fderiv_fiberMap_single w a z hY]
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, quaternionFiberJacobian,
    complexK_star, ← map_mul, ← Finset.sum_mul, ← Finset.smul_sum]

private theorem gradient_pairing_algebra {ι : Type*} [Fintype ι]
    (u v : ι → Quaternion ℝ) :
    (∑ b, star ((2 : ℝ) • (u b * qi)) * v b) =
      (2 : ℝ) • (star qi * (star u ⬝ᵥ v)) := by
  simp only [Quaternion.star_smul, star_mul, smul_mul_assoc, Finset.smul_sum,
    dotProduct, Pi.star_apply, Finset.mul_sum, mul_assoc]

/-- The full Hessian kernel is orthogonal to the actual defining-function gradient. -/
theorem fiberHessian_kernel_orthogonal_gradient {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) (v : Index d → Quaternion ℝ)
    (hH : fiberHessian w a z *ᵥ v = 0) : star (fiberGradient w a z) ⬝ᵥ v = 0 := by
  have hJ := (fiberHessian_kernel_iff w a z hY v).mp hH
  have hp : star ((quaternionFiberJacobian w a z)ᴴ *ᵥ
      (fun i => complexK (fiberMap w a z i))) ⬝ᵥ v = 0 := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, ← Matrix.dotProduct_mulVec,
      hJ, dotProduct_zero]
  simp only [dotProduct, Pi.star_apply, fiberGradient_formula w a z hY]
  rw [gradient_pairing_algebra, hp, mul_zero, smul_zero]

theorem fiberHessian_kernel_tangent_phi {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (v : Index d → Quaternion ℝ) (ha : a ≠ 0) (hY : z none ≠ 0)
    (hH : fiberHessian w a z *ᵥ v = 0) :
    (∑ b, complexK (phaseRow (ratio z) b) * v b) = 0 := by
  have hJ := congrFun ((fiberHessian_kernel_iff w a z hY v).mp hH) none
  have he : complexK (10 / (a : ℂ)) * (∑ b, complexK (phaseRow (ratio z) b) * v b) = 0 := by
    simpa only [Matrix.mulVec, dotProduct, quaternionFiberJacobian, fiberJacobian,
      map_mul, mul_assoc, ← Finset.mul_sum, Pi.zero_apply] using hJ
  have hc : complexK (10 / (a : ℂ)) ≠ 0 := by
    intro hz
    have heq := congrArg quaternionFirst hz
    change (10 / (a : ℂ)) = 0 at heq
    have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
    exact (div_ne_zero (by norm_num) haC) heq
  exact (mul_eq_zero.mp he).resolve_left hc

theorem fderiv_phi_single {d : ℕ} (z : Index d → ℂ) (hY : z none ≠ 0) (b : Index d) :
    fderiv ℂ (phi : (Index d → ℂ) → ℂ) z (Pi.single b 1) = phaseRow (ratio z) b := by
  have he : (fun q : Index d → ℂ => fiberMap 1 10 q none) = phi := by
    funext q
    simp [fiberMap]
  have hh := fderiv_fiberMap_single 1 10 z hY none b
  rw [he] at hh
  simpa [fiberJacobian] using hh

def backgroundHessian {d : ℕ} (z : Index d → ℂ) :
    Matrix (Index d) (Index d) (Quaternion ℝ) :=
  OAI.Analysis.Calculus.Quaternion.imaginaryHessian (fun q => ‖phi q‖ ^ 2) z

theorem backgroundHessian_formula {d : ℕ} (z : Index d → ℂ) (hY : z none ≠ 0) :
    backgroundHessian z = (4 : ℝ) •
      OAI.Analysis.Calculus.Quaternion.outer (fun b => complexK (star (phaseRow (ratio z) b))) := by
  have he : (fun q : Index d → ℂ => fiberMap 1 10 q none) = phi := by
    funext q
    simp [fiberMap]
  have hf : ContDiffAt ℂ 2 (phi : (Index d → ℂ) → ℂ) z := by
    rw [← he]
    exact contDiffAt_fiberMap_complex 1 10 z hY none
  apply Matrix.ext
  intro a b
  simp only [backgroundHessian, OAI.Analysis.Calculus.Quaternion.imaginaryHessian_norm_sq hf, fderiv_phi_single z hY,
    Matrix.smul_apply, OAI.Analysis.Calculus.Quaternion.outer, ← complexK_star, star_star, map_mul]

/-- The full fiber Hessian and the rank-one background have the required common kernel. -/
theorem fiberHessian_kernel_background {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (v : Index d → Quaternion ℝ) (ha : a ≠ 0) (hY : z none ≠ 0)
    (hH : fiberHessian w a z *ᵥ v = 0) : backgroundHessian z *ᵥ v = 0 := by
  have ht := fiberHessian_kernel_tangent_phi w a z v ha hY hH
  rw [backgroundHessian_formula z hY, Matrix.smul_mulVec]
  have hz : OAI.Analysis.Calculus.Quaternion.outer (fun b => complexK (star (phaseRow (ratio z) b))) *ᵥ v = 0 := by
    funext b
    rw [OAI.Analysis.Calculus.Quaternion.outer_mulVec]
    simp only [← complexK_star, star_star, ht, mul_zero, Pi.zero_apply]
  rw [hz, smul_zero]

end
end OAI.Analysis.Calculus.Current
