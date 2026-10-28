import OAI.RepresentationTheory.Theta.Kernel.IntrinsicMatrixAnalytic

/-! # Intrinsic Tensor Analytic -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicTensorAnalytic.Intrinsic

noncomputable section

/-! Analytic change of all covariant slots of a continuous multilinear
tensor by a varying invertible matrix. -/

open scoped Classical _root_.Matrix _root_.Matrix.Norms.Elementwise ContDiff

variable {I : Type} [Fintype I] [DecidableEq I]

def matrixLinear : Matrix I I ℂ →L[ℂ] ((I → ℂ) →L[ℂ] (I → ℂ)) :=
  (LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toLin'.toLinearMap).toContinuousLinearMap

theorem matrixLinear_apply (M : Matrix I I ℂ) :
    matrixLinear M = (Matrix.toLin' M).toContinuousLinearMap := rfl

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {x : V}

theorem inverseTransposeLinear_analytic (M : V → Matrix I I ℂ)
    (hM : ContDiffAt ℂ ⊤ M x) (hdet : (M x).det ≠ 0) :
    ContDiffAt ℂ ⊤ (fun q => matrixLinear (M q)⁻¹ᵀ) x := by
  apply ContDiffAt.comp (f := fun q => (M q)⁻¹ᵀ)
    (g := matrixLinear (I := I)) x (matrixLinear (I := I)).contDiff.contDiffAt
  have hi := IntrinsicMatrixAnalytic.Intrinsic.matrix_inverse_contDiffAt M hM hdet
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  exact (contDiff_apply ℂ ℂ i).contDiffAt.comp x
    ((contDiff_apply ℂ (I → ℂ) j).contDiffAt.comp x hi)

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {w : W}

omit [DecidableEq I] in
theorem tensor_precomposition_analytic (a : ℕ)
    (T : W → ContinuousMultilinearMap ℂ (fun _ : Fin a => I → ℂ) ℂ)
    (L : W → (I → ℂ) →L[ℂ] (I → ℂ))
    (hT : ContDiffAt ℝ ⊤ T w) (hL : ContDiffAt ℝ ⊤ L w) :
    ContDiffAt ℝ ⊤ (fun q => (T q).compContinuousLinearMap (fun _ => L q)) w := by
  have hd : ContDiffAt ℝ ⊤ (fun q : W => fun _ : Fin a => L q) w :=
    contDiffAt_pi.mpr (fun _ => hL)
  have hp : ContDiffAt ℂ ⊤
      (fun p : (Fin a → (I → ℂ) →L[ℂ] (I → ℂ)) ×
        ContinuousMultilinearMap ℂ (fun _ : Fin a => I → ℂ) ℂ =>
          p.2.compContinuousLinearMap p.1) ((fun _ => L w),T w) :=
    ContinuousMultilinearMap.cpolynomialAt_uncurry_compContinuousLinearMap.contDiffAt
  exact ContDiffAt.comp
    (f := fun q => ((fun _ : Fin a => L q),T q))
    (g := fun p : (Fin a → (I → ℂ) →L[ℂ] (I → ℂ)) ×
        ContinuousMultilinearMap ℂ (fun _ : Fin a => I → ℂ) ℂ =>
          p.2.compContinuousLinearMap p.1)
    w (hp.restrict_scalars ℝ) (hd.prodMk hT)

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicTensorAnalytic.Intrinsic
