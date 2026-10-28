import Mathlib

/-! # Tensor Smoothness -/

namespace OAI.RepresentationTheory.Theta.Adelic.TensorSmoothness

noncomputable section

/-! Smooth change of frame for finite complex multilinear tensors. -/

open scoped Classical _root_.Matrix.Norms.Elementwise

open _root_.Matrix

variable {I : Type} [Fintype I] [DecidableEq I]

def matrixOperator : Matrix I I ℂ →ₗ[ℂ] ((I → ℂ) →L[ℂ] (I → ℂ)) :=
  LinearMap.comp LinearMap.toContinuousLinearMap.toLinearMap Matrix.toLin'.toLinearMap

theorem matrixOperator_contDiff :
    ContDiff ℝ ⊤ (fun M : Matrix I I ℂ => (Matrix.toLin' M).toContinuousLinearMap) :=
  (matrixOperator (I := I)).toContinuousLinearMap.contDiff.restrict_scalars ℝ

omit [DecidableEq I] in
theorem matrix_transpose_contDiff :
    ContDiff ℝ ⊤ (fun M : Matrix I I ℂ => Mᵀ) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact contDiff_apply_apply ℝ ℂ j i

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {s : Set V}

omit [DecidableEq I] in
theorem tensor_frame_smooth (a : ℕ)
    (T : V → ContinuousMultilinearMap ℂ (fun _ : Fin a => I → ℂ) ℂ)
    (M : V → (I → ℂ) →L[ℂ] (I → ℂ))
    (hT : ContDiffOn ℝ ⊤ T s) (hM : ContDiffOn ℝ ⊤ M s) :
    ContDiffOn ℝ ⊤ (fun z => (T z).compContinuousLinearMap (fun _ => M z)) s := by
  have hc : ContDiff ℂ ⊤
      (fun p : (Fin a → (I → ℂ) →L[ℂ] (I → ℂ)) ×
        ContinuousMultilinearMap ℂ (fun _ : Fin a => I → ℂ) ℂ =>
          p.2.compContinuousLinearMap p.1) :=
    (ContinuousMultilinearMap.analyticOnNhd_uncurry_compContinuousLinearMap
      (t := Set.univ)).contDiff
  exact (hc.restrict_scalars ℝ).comp_contDiffOn
    ((contDiffOn_pi.mpr (fun _ => hM)).prodMk hT)

end

end OAI.RepresentationTheory.Theta.Adelic.TensorSmoothness
