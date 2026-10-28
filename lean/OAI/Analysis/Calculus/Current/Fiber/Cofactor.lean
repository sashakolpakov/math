import OAI.Analysis.Calculus.Current.Fiber.Normal
import OAI.Analysis.Calculus.Quaternion.IndexedCofactor

/-! The genuine Moore-cofactor regularizer of the fiber defining function. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped Matrix Matrix.Norms.Elementwise ComplexOrder ContDiff

def fiberCofactor {d : ℕ} (w a : ℝ) (z : Index d → ℂ) :
    Matrix (Index d) (Index d) (Quaternion ℝ) := OAI.Analysis.Calculus.Quaternion.indexedCofactor (fiberHessian w a z)

theorem fiberHessian_isHermitian {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) : (fiberHessian w a z).IsHermitian := by
  rw [fiberHessian_factorization w a z hY]
  apply Matrix.ext
  intro i j
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Quaternion.star_smul,
    Matrix.mul_apply, star_sum, star_mul, star_star]

theorem fiberHessian_posSemidef {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) : (OAI.LinearAlgebra.Moore.complexify (fiberHessian w a z)).PosSemidef :=
  (OAI.Analysis.Calculus.Quaternion.indexed_complexify_posSemidef_iff _ (fiberHessian_isHermitian w a z hY)).mpr
    (fiberHessian_nonneg w a z hY)

theorem fiberHessian_mooreDet_zero {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) : OAI.Analysis.Calculus.Quaternion.indexedMooreDet (fiberHessian w a z) = 0 := by
  apply OAI.Analysis.Calculus.Quaternion.indexedMooreDet_zero_of_kernel _ (fiberHessian_isHermitian w a z hY)
    (fun b => complexK (fiberKernelVector z b)) _ (fiberHessian_kernel w a z hY)
  intro hz
  have h := congrFun hz none
  simp [fiberKernelVector] at h

theorem fiberCofactor_isHermitian {d : ℕ} (w a : ℝ) (z : Index d → ℂ) :
    (fiberCofactor w a z).IsHermitian := OAI.Analysis.Calculus.Quaternion.indexedCofactor_isHermitian _

theorem fiberCofactor_posSemidef {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) : (OAI.LinearAlgebra.Moore.complexify (fiberCofactor w a z)).PosSemidef :=
  OAI.Analysis.Calculus.Quaternion.indexedCofactor_posSemidef _ (fiberHessian_posSemidef w a z hY)

theorem fiberCofactor_nonneg {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) (v : Index d → Quaternion ℝ) :
    0 ≤ (star v ⬝ᵥ (fiberCofactor w a z *ᵥ v)).re :=
  (OAI.Analysis.Calculus.Quaternion.indexed_complexify_posSemidef_iff _ (fiberCofactor_isHermitian w a z)).mp
    (fiberCofactor_posSemidef w a z hY) v

theorem fiberCofactor_image_in_kernel {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) (v : Index d → Quaternion ℝ) :
    fiberHessian w a z *ᵥ (fiberCofactor w a z *ᵥ v) = 0 :=
  OAI.Analysis.Calculus.Quaternion.indexedCofactor_image_in_kernel _ (fiberHessian_isHermitian w a z hY)
    (fiberHessian_mooreDet_zero w a z hY) v

theorem fiberCofactor_tangent_phi {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (ha : a ≠ 0) (hY : z none ≠ 0) (v : Index d → Quaternion ℝ) :
    (∑ b, complexK (phaseRow (ratio z) b) * (fiberCofactor w a z *ᵥ v) b) = 0 :=
  fiberHessian_kernel_tangent_phi w a z _ ha hY (fiberCofactor_image_in_kernel w a z hY v)

theorem fiberCofactor_orthogonal_gradient {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) (v : Index d → Quaternion ℝ) :
    star (fiberGradient w a z) ⬝ᵥ (fiberCofactor w a z *ᵥ v) = 0 :=
  fiberHessian_kernel_orthogonal_gradient w a z hY _ (fiberCofactor_image_in_kernel w a z hY v)

theorem fiberCofactor_background {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (ha : a ≠ 0) (hY : z none ≠ 0) (v : Index d → Quaternion ℝ) :
    backgroundHessian z *ᵥ (fiberCofactor w a z *ᵥ v) = 0 :=
  fiberHessian_kernel_background w a z _ ha hY (fiberCofactor_image_in_kernel w a z hY v)

theorem fiberHessian_pos_on_Y_zero {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hw : w ≠ 0) (ha : a ≠ 0) (hY : z none ≠ 0) (v : Index d → Quaternion ℝ)
    (hv : v ≠ 0) (hvY : v none = 0) :
    0 < (star v ⬝ᵥ (fiberHessian w a z *ᵥ v)).re := by
  have hJ : quaternionFiberJacobian w a z *ᵥ v ≠ 0 := by
    intro h
    apply hv
    have he := quaternionFiberJacobian_kernel_unique w a z v hw ha hY h
    funext b
    simp only [congrFun he b, hvY, mul_zero, Pi.zero_apply]
  rw [fiberHessian_factorization w a z hY, Matrix.smul_mulVec, dotProduct_smul]
  simpa only [Quaternion.re_smul, smul_eq_mul] using
    mul_pos (by norm_num : (0 : ℝ) < 4)
      (OAI.Analysis.Calculus.Quaternion.quaternionGram_pos (quaternionFiberJacobian w a z) v hJ)

theorem fiberCofactor_YY_pos {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hw : w ≠ 0) (ha : a ≠ 0) (hY : z none ≠ 0) :
    0 < (fiberCofactor w a z none none).re :=
  OAI.Analysis.Calculus.Quaternion.indexedCofactor_diag_pos _ none (fiberHessian_posSemidef w a z hY)
    (fiberHessian_mooreDet_zero w a z hY) (fiberHessian_pos_on_Y_zero w a z hw ha hY)

theorem fiberCofactor_divergence_zero {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) (b : Index d) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence OAI.Analysis.Calculus.Quaternion.threeSlots (fun p => fderiv ℝ (fiberCofactor w a) z
      (OAI.Analysis.Calculus.Quaternion.imaginaryDirection p.1 p.2)) b = 0 := by
  exact OAI.Analysis.Calculus.Quaternion.indexedCofactor_directionalHessian_divergence OAI.Analysis.Calculus.Quaternion.threeSlots
    (fun p => OAI.Analysis.Calculus.Quaternion.imaginaryDirection p.1 p.2)
    ((contDiffAt_fiberDefining w a z hY).of_le (by simp)) b

theorem contDiffAt_fiberHessian {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) : ContDiffAt ℝ ⊤ (fiberHessian w a) z := by
  have hH : ContDiffAt ℝ ⊤ (fderiv ℝ (fderiv ℝ (fiberDefining w a))) z :=
    ((contDiffAt_fiberDefining w a z hY).fderiv_right (m := ⊤) (by simp)).fderiv_right
      (m := ⊤) (by simp)
  have he : ContDiffAt ℝ ⊤
      (OAI.Analysis.Calculus.Quaternion.directionalRealHessian (fun p => OAI.Analysis.Calculus.Quaternion.imaginaryDirection (ι := Index d) p.1 p.2)
        (fiberDefining w a)) z := by
    apply contDiffAt_pi.mpr
    intro p
    apply contDiffAt_pi.mpr
    intro q
    exact (hH.clm_apply contDiffAt_const).clm_apply contDiffAt_const
  simpa only using! (OAI.Analysis.Calculus.Quaternion.hessianCLM OAI.Analysis.Calculus.Quaternion.threeSlots).contDiff.contDiffAt.comp z he

theorem contDiffAt_fiberCofactor {d : ℕ} (w a : ℝ) (z : Index d → ℂ)
    (hY : z none ≠ 0) : ContDiffAt ℝ ⊤ (fiberCofactor w a) z :=
  (OAI.Analysis.Calculus.Quaternion.contDiff_indexedCofactor ⊤).contDiffAt.comp z (contDiffAt_fiberHessian w a z hY)

end OAI.Analysis.Calculus.Current
