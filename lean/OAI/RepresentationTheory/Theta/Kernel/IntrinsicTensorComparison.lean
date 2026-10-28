import OAI.RepresentationTheory.Theta.Kernel.IntrinsicComparison
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitFactorization
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicDeterminantComparison

/-! # Intrinsic Tensor Comparison -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicTensorComparison.Intrinsic

noncomputable section

/-! Differentiating the checked completed-kernel comparison identifies
the actual native order-two tensors and their ordinary top forms. -/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise ContDiff

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicGlobal OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitTensor.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicAnalysis.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitFactorization.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicComparison.IntrinsicKernel
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicQuadraticPhase.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionMatrices.IntrinsicShearComparison OAI.RepresentationTheory.Theta.Kernel.IntrinsicDeterminantComparison.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {S : IntrinsicSplitting.IntrinsicSummands.SecondLine A}
variable {P₁ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₁} {P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H S.form}
variable (B₁ : Adelic.DataTheta.ComparisonData F H K₁ A)
variable (B₂ : Adelic.DataTheta.ComparisonData F H S.form (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
variable (B : Adelic.DataTheta.ComparisonData F H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S))

theorem splitKernel_contDiff
    (hE₁ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hE₂ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)))
    (hTensorDecomposition : DerivativeFactorizationPrerequisites.Prerequisites.TensorDecomposition.Statement.{0, 0, 0, 0})
    (hΘ₁ : Adelic.DataTheta.Descent.ThetaConstruction B₁) (hΘ₂ : Adelic.DataTheta.Descent.ThetaConstruction B₂)
    (g : Adelic.FiniteSchwartz.finiteSchwartz F 6) (z : Adelic.BallNatural.Ball) : ContDiff ℂ ⊤ (IntrinsicSplitTensor.Intrinsic.splitKernel B₁ B₂ g z) := by
  obtain ⟨n,a,b,he⟩ := IntrinsicSplitFactorization.Intrinsic.input_products hTensorDecomposition g
  rw [IntrinsicSplitFactorization.Intrinsic.splitKernel_finite_sum B₁ B₂ hΘ₁ hΘ₂ g n a b he z]
  exact ContDiff.sum (fun j _ => IntrinsicSplitFactorization.Intrinsic.splitKernel_product_contDiff B₁ B₂ hE₁ hE₂ hΘ₁ hΘ₂ (a j) (b j) z)

theorem native_hessian_comparison
    (hC₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁) (hC₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hG₁ : Adelic.DataTheta.GeometryIdentification B₁) (hG₂ : Adelic.DataTheta.GeometryIdentification B₂)
    (hG : Adelic.DataTheta.GeometryIdentification B)
    (hE₁ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hE₂ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)))
    (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)))
    (hTensorDecomposition : DerivativeFactorizationPrerequisites.Prerequisites.TensorDecomposition.Statement.{0, 0, 0, 0})
    (hΘ₁ : Adelic.DataTheta.Descent.ThetaConstruction B₁) (hΘ₂ : Adelic.DataTheta.Descent.ThetaConstruction B₂) (hΘ : Adelic.DataTheta.Descent.ThetaConstruction B)
    (f g : Adelic.FiniteSchwartz.finiteSchwartz F 6)
    (hweight : ∀ x : Fin 6 → F, Adelic.Evaluation.finiteSchwartzFunction F 6 g (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
      IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F 6 (-IntrinsicPositionMatrices.IntrinsicShearComparison.shearBilinear B₁ B₂ B) x *
        Adelic.Evaluation.finiteSchwartzFunction F 6 f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x)) (z : Adelic.BallNatural.Ball) :
    (iteratedFDeriv ℂ 2 (IntrinsicSplitTensor.Intrinsic.splitKernel B₁ B₂ g z) 0).compContinuousLinearMap
        (fun _ => IntrinsicSplitTensor.Intrinsic.splitJacobi B₁ B₂ z) =
      (iteratedFDeriv ℂ 2 (Adelic.DataTheta.completedTheta B f (B.period z).matrix) 0).compContinuousLinearMap
        (fun _ => (Matrix.toLin' (B.frame z).invᵀ).toContinuousLinearMap) := by
  let L := (Matrix.toLin' (B.frame z).invᵀ).toContinuousLinearMap
  have he : IntrinsicSplitTensor.Intrinsic.splitKernel B₁ B₂ g z ∘ IntrinsicSplitTensor.Intrinsic.splitJacobi B₁ B₂ z =
      Adelic.DataTheta.completedTheta B f (B.period z).matrix ∘ L := by
    funext u
    exact IntrinsicComparison.IntrinsicKernel.completed_kernel_comparison_of_weights B₁ B₂ B hC₁ hC₂ hC hG₁ hG₂ hG f g hweight z u
  have h := congrArg (fun p => iteratedFDeriv ℂ 2 p 0) he
  rw [(IntrinsicSplitTensor.Intrinsic.splitJacobi B₁ B₂ z).iteratedFDeriv_comp_right
    (splitKernel_contDiff B₁ B₂ hE₁ hE₂ hTensorDecomposition hΘ₁ hΘ₂ g z) 0 (show (2 : ℕ∞ω) ≤ ⊤ from le_top),
    L.iteratedFDeriv_comp_right (IntrinsicAnalysis.Intrinsic.completed_contDiff B hE hΘ f (B.period z))
      0 (show (2 : ℕ∞ω) ≤ ⊤ from le_top)] at h
  simpa only [map_zero] using h

theorem native_tensor_comparison
    (hC₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁) (hC₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hG₁ : Adelic.DataTheta.GeometryIdentification B₁) (hG₂ : Adelic.DataTheta.GeometryIdentification B₂)
    (hG : Adelic.DataTheta.GeometryIdentification B)
    (hE₁ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex A))
    (hE₂ : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S)))
    (hE : Analysis.GaussianConvergenceInput (Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S)))
    (hTensorDecomposition : DerivativeFactorizationPrerequisites.Prerequisites.TensorDecomposition.Statement.{0, 0, 0, 0})
    (hΘ₁ : Adelic.DataTheta.Descent.ThetaConstruction B₁) (hΘ₂ : Adelic.DataTheta.Descent.ThetaConstruction B₂) (hΘ : Adelic.DataTheta.Descent.ThetaConstruction B)
    (f g : Adelic.FiniteSchwartz.finiteSchwartz F 6)
    (hweight : ∀ x : Fin 6 → F, Adelic.Evaluation.finiteSchwartzFunction F 6 g (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
      IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F 6 (-IntrinsicPositionMatrices.IntrinsicShearComparison.shearBilinear B₁ B₂ B) x *
        Adelic.Evaluation.finiteSchwartzFunction F 6 f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x)) (z : Adelic.BallNatural.Ball) :
    Adelic.DataTheta.geometricTensor B f 2 z = (IntrinsicDeterminantComparison.Intrinsic.halfFrameRatio B₁ B₂ B z)⁻¹ • IntrinsicSplitTensor.Intrinsic.splitGeometricTensor B₁ B₂ g z := by
  have hess := native_hessian_comparison B₁ B₂ B hC₁ hC₂ hC hG₁ hG₂ hG
    hE₁ hE₂ hE hTensorDecomposition hΘ₁ hΘ₂ hΘ f g hweight z
  have hscale : (B.halfFrame z)⁻¹ =
      (IntrinsicDeterminantComparison.Intrinsic.halfFrameRatio B₁ B₂ B z)⁻¹ * (B₁.halfFrame z * B₂.halfFrame z)⁻¹ := by
    unfold IntrinsicDeterminantComparison.Intrinsic.halfFrameRatio
    field_simp [(hG.2.2.2.2.2.1 z).1, (hG₁.2.2.2.2.2.1 z).1, (hG₂.2.2.2.2.2.1 z).1]
  have hscalar (w : ℂ) : (B.halfFrame z)⁻¹ * ((2 : ℂ)⁻¹ * w) =
      (IntrinsicDeterminantComparison.Intrinsic.halfFrameRatio B₁ B₂ B z)⁻¹ *
        ((B₁.halfFrame z * B₂.halfFrame z)⁻¹ * ((2 : ℂ)⁻¹ * w)) := by
    rw [hscale]
    ring
  apply ContinuousMultilinearMap.ext
  intro v
  have hv := congrArg (fun T : Adelic.DataTheta.TaylorTensor (A := IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) 2 => T v) hess
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at hv
  change (B.halfFrame z)⁻¹ * ((Nat.factorial 2 : ℂ)⁻¹ *
      iteratedFDeriv ℂ 2 (Adelic.DataTheta.completedTheta B f (B.period z).matrix) 0
        (fun i => (Matrix.toLin' (B.frame z).invᵀ).toContinuousLinearMap (v i))) =
    (IntrinsicDeterminantComparison.Intrinsic.halfFrameRatio B₁ B₂ B z)⁻¹ * ((B₁.halfFrame z * B₂.halfFrame z)⁻¹ *
      ((2 : ℂ)⁻¹ * iteratedFDeriv ℂ 2 (IntrinsicSplitTensor.Intrinsic.splitKernel B₁ B₂ g z) 0
        (fun i => IntrinsicSplitTensor.Intrinsic.splitJacobi B₁ B₂ z (v i))))
  rw [show (Nat.factorial 2 : ℂ) = 2 by norm_num, ← hv]
  exact hscalar _

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicTensorComparison.Intrinsic
