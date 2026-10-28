import Mathlib

/-! # Intrinsic Matrix Analytic -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicMatrixAnalytic.Intrinsic

noncomputable section

/-! Ambient analytic matrix calculus in the elementwise topology. -/

open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise ContDiff

variable {V I : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable [Fintype I] [DecidableEq I] {x : V}

theorem matrix_determinant_contDiffAt (M : V → Matrix I I ℂ) (hM : ContDiffAt ℂ ⊤ M x) :
    ContDiffAt ℂ ⊤ (fun z => (M z).det) x := by
  simp only [Matrix.det_apply']
  fun_prop

theorem matrix_inverse_contDiffAt (M : V → Matrix I I ℂ) (hM : ContDiffAt ℂ ⊤ M x)
    (hdet : (M x).det ≠ 0) : ContDiffAt ℂ ⊤ (fun z => (M z)⁻¹) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  simp only [Matrix.inv_def,Ring.inverse_eq_inv,Matrix.smul_apply,smul_eq_mul,Matrix.adjugate_apply]
  apply ContDiffAt.mul
  · exact (matrix_determinant_contDiffAt M hM).inv hdet
  · apply matrix_determinant_contDiffAt
    apply contDiffAt_pi.mpr
    intro k
    apply contDiffAt_pi.mpr
    intro l
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact contDiffAt_const
    · fun_prop

omit [DecidableEq I] in
theorem matrix_product_contDiffAt (M N : V → Matrix I I ℂ)
    (hM : ContDiffAt ℂ ⊤ M x) (hN : ContDiffAt ℂ ⊤ N x) :
    ContDiffAt ℂ ⊤ (fun z => M z * N z) x := by
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  simp only [Matrix.mul_apply]
  fun_prop

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicMatrixAnalytic.Intrinsic
