import Mathlib

/-! # Matrix Smoothness -/

namespace OAI.RepresentationTheory.Theta.Adelic.MatrixSmoothness

noncomputable section

/-! Smooth finite matrix operations in the actual elementwise topology. -/

open scoped Classical _root_.Matrix.Norms.Elementwise

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem matrix_determinant_contDiff : ContDiff ℝ ⊤ (Matrix.det : Matrix I I ℂ → ℂ) := by
  change ContDiff ℝ ⊤ (fun M : Matrix I I ℂ => M.det)
  simp only [Matrix.det_apply']
  fun_prop

theorem matrix_adjugate_contDiff : ContDiff ℝ ⊤ (Matrix.adjugate : Matrix I I ℂ → Matrix I I ℂ) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [Matrix.adjugate_apply]
  apply matrix_determinant_contDiff.comp
  apply contDiff_pi.mpr
  intro k
  apply contDiff_pi.mpr
  intro l
  simp only [Matrix.updateRow_apply]
  split_ifs <;> fun_prop

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {s : Set V}

theorem matrix_inverse_contDiffOn (M : V → Matrix I I ℂ)
    (hM : ContDiffOn ℝ ⊤ M s) (hn : ∀ z ∈ s, (M z).det ≠ 0) :
    ContDiffOn ℝ ⊤ (fun z => (M z)⁻¹) s := by
  have hd := matrix_determinant_contDiff.comp_contDiffOn hM
  have ha := matrix_adjugate_contDiff.comp_contDiffOn hM
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact (hd.inv hn).mul ((contDiff_apply ℝ ℂ j).comp_contDiffOn ((contDiff_apply ℝ (I → ℂ) i).comp_contDiffOn ha))

omit [DecidableEq I] in
theorem matrix_product_contDiffOn (M N : V → Matrix I I ℂ)
    (hM : ContDiffOn ℝ ⊤ M s) (hN : ContDiffOn ℝ ⊤ N s) :
    ContDiffOn ℝ ⊤ (fun z => M z * N z) s := by
  apply contDiffOn_pi.mpr
  intro i
  apply contDiffOn_pi.mpr
  intro j
  simp only [Matrix.mul_apply]
  fun_prop

end

end OAI.RepresentationTheory.Theta.Adelic.MatrixSmoothness
