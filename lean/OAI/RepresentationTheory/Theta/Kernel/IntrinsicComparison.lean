import OAI.RepresentationTheory.Theta.Kernel.IntrinsicJacobiComparison
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicQuadraticPhase

/-! # Intrinsic Comparison -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicComparison.IntrinsicKernel

noncomputable section

/-! Exact comparison of the native total and split completed kernels.
The finite input change is constructed from their rational shear and is
independent of both the ball point and the Jacobi variable. -/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicGlobal
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockSiegel.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockCompletion.IntrinsicKernel OAI.RepresentationTheory.Theta.Kernel.IntrinsicPhaseTransport.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionMatrices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionMatrices.IntrinsicShearComparison OAI.RepresentationTheory.Theta.Kernel.IntrinsicJacobiComparison.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitTensor.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicQuadraticPhase.Intrinsic

theorem quadraticPhase_neg_mul {F : Type} [Field F] [NumberField F] (N : ℕ)
    (Q : (Fin N → F) →ₗ[ℚ] (Fin N → F) →ₗ[ℚ] ℚ) (x : Fin N → F) :
    IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F N (-Q) x * IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F N Q x = 1 := by
  change Complex.exp ((Real.pi : ℂ) * Complex.I * ((-(Q x x) : ℚ) : ℂ)) *
    Complex.exp ((Real.pi : ℂ) * Complex.I * ((Q x x : ℚ) : ℂ)) = 1
  rw [Rat.cast_neg, ← Complex.exp_add]
  convert Complex.exp_zero using 1
  congr 1
  ring

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {S : IntrinsicSplitting.IntrinsicSummands.SecondLine A}
variable {P₁ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₁} {P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H S.form}
variable (B₁ : Adelic.DataTheta.ComparisonData F H K₁ A)
variable (B₂ : Adelic.DataTheta.ComparisonData F H S.form (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
variable (B : Adelic.DataTheta.ComparisonData F H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S))

theorem bare_kernel_frame_comparison
    (hC₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁) (hC₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hG₁ : Adelic.DataTheta.GeometryIdentification B₁) (hG₂ : Adelic.DataTheta.GeometryIdentification B₂)
    (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball)
    (u : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) (x : Fin 6 → F) :
    IntrinsicBlockCompletion.IntrinsicKernel.kernel (IntrinsicBlockSiegel.Intrinsic.blockPeriod (B₁.period z) (B₂.period z)).matrix (IntrinsicSplitTensor.Intrinsic.splitJacobi B₁ B₂ z u)
      (fun i => (IntrinsicBlockCompletion.IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition x i : ℝ)) =
      IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F 6 (IntrinsicPositionMatrices.IntrinsicShearComparison.shearBilinear B₁ B₂ B) x *
        Adelic.DataTheta.gaussianValue (B.period z).matrix ((B.frame z).invᵀ.mulVec u)
          (fun i => (B.rationalPosition x i : ℝ)) := by
  have hR : (IntrinsicPositionMatrices.Intrinsic.positionMatrix B₁ B₂ B).mulVec (fun i => (B.rationalPosition x i : ℂ)) =
      fun i => (IntrinsicBlockCompletion.IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition x i : ℂ) := by
    rw [IntrinsicPositionMatrices.Intrinsic.positionMatrix_apply B₁ B₂ B hC₁ hC₂ hC,
      IntrinsicPositionMatrices.IntrinsicShearComparison.complexPositionChange_rational B₁ B₂ B hC₁ hC₂ hC]
    change (fun i => (IntrinsicBlockCompletion.IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition
      (B.rationalPosition.symm (B.rationalPosition x)) i : ℂ)) = _
    rw [LinearEquiv.symm_apply_apply]
  have hlin :
      (∑ i, ((IntrinsicBlockCompletion.IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition x i : ℝ) : ℂ) *
        IntrinsicSplitTensor.Intrinsic.splitJacobi B₁ B₂ z u i) =
      ∑ i, ((B.rationalPosition x i : ℝ) : ℂ) * (B.frame z).invᵀ.mulVec u i := by
    have h := Matrix.dotProduct_transpose_mulVec (IntrinsicPositionMatrices.Intrinsic.positionMatrix B₁ B₂ B)
      (fun i => (B.rationalPosition x i : ℂ)) (IntrinsicSplitTensor.Intrinsic.splitJacobi B₁ B₂ z u)
    rw [← IntrinsicJacobiComparison.Intrinsic.native_jacobi_relation B₁ B₂ B hC₁ hC₂ hC hG₁ hG₂ hG, hR] at h
    simpa only [Complex.ofReal_ratCast, dotProduct] using
      (h.trans (dotProduct_comm _ _)).symm
  have hq := IntrinsicPositionMatrices.IntrinsicShearComparison.native_quadratic_difference B₁ B₂ B hC₁ hC₂ hC hG₁ hG₂ hG z x
  have hq' : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (IntrinsicBlockSiegel.Intrinsic.blockPeriod (B₁.period z) (B₂.period z)).matrix
      (fun i => (IntrinsicBlockCompletion.IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition x i : ℝ))
      (fun i => (IntrinsicBlockCompletion.IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition x i : ℝ)) =
    AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (B.period z).matrix (fun i => (B.rationalPosition x i : ℝ))
      (fun i => (B.rationalPosition x i : ℝ)) + ((IntrinsicPositionMatrices.IntrinsicShearComparison.shearBilinear B₁ B₂ B x x : ℚ) : ℂ) := by
    linear_combination hq
  unfold IntrinsicBlockCompletion.IntrinsicKernel.kernel Adelic.DataTheta.gaussianValue IntrinsicQuadraticPhase.Intrinsic.quadraticPhase
  rw [← Complex.exp_add, hq', hlin]
  congr 1
  ring

theorem completed_kernel_comparison_of_weights
    (hC₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁) (hC₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hG₁ : Adelic.DataTheta.GeometryIdentification B₁) (hG₂ : Adelic.DataTheta.GeometryIdentification B₂)
    (hG : Adelic.DataTheta.GeometryIdentification B) (f g : Adelic.FiniteSchwartz.finiteSchwartz F 6)
    (hweight : ∀ x : Fin 6 → F, Adelic.Evaluation.finiteSchwartzFunction F 6 g (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
      IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F 6 (-IntrinsicPositionMatrices.IntrinsicShearComparison.shearBilinear B₁ B₂ B) x *
        Adelic.Evaluation.finiteSchwartzFunction F 6 f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x))
    (z : Adelic.BallNatural.Ball) (u : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) :
    IntrinsicSplitTensor.Intrinsic.splitKernel B₁ B₂ g z (IntrinsicSplitTensor.Intrinsic.splitJacobi B₁ B₂ z u) =
      Adelic.DataTheta.completedTheta B f (B.period z).matrix ((B.frame z).invᵀ.mulVec u) := by
  have ht : IntrinsicBlockCompletion.IntrinsicKernel.literalTheta (IntrinsicBlockCompletion.IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition) g
      (IntrinsicBlockSiegel.Intrinsic.blockPeriod (B₁.period z) (B₂.period z)).matrix (IntrinsicSplitTensor.Intrinsic.splitJacobi B₁ B₂ z u) =
        Adelic.DataTheta.rationalTheta B f (B.period z).matrix ((B.frame z).invᵀ.mulVec u) := by
    apply tsum_congr
    intro x
    change Adelic.Evaluation.finiteSchwartzFunction F 6 g (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) *
        IntrinsicBlockCompletion.IntrinsicKernel.kernel (IntrinsicBlockSiegel.Intrinsic.blockPeriod (B₁.period z) (B₂.period z)).matrix (IntrinsicSplitTensor.Intrinsic.splitJacobi B₁ B₂ z u)
          (fun i => (IntrinsicBlockCompletion.IntrinsicKernel.blockPosition B₁.rationalPosition B₂.rationalPosition x i : ℝ)) =
      Adelic.Evaluation.finiteSchwartzFunction F 6 f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) *
        Adelic.DataTheta.gaussianValue (B.period z).matrix ((B.frame z).invᵀ.mulVec u)
          (fun i => (B.rationalPosition x i : ℝ))
    rw [hweight, bare_kernel_frame_comparison B₁ B₂ B hC₁ hC₂ hC hG₁ hG₂ hG]
    calc
      _ = (IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F 6 (-IntrinsicPositionMatrices.IntrinsicShearComparison.shearBilinear B₁ B₂ B) x *
          IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F 6 (IntrinsicPositionMatrices.IntrinsicShearComparison.shearBilinear B₁ B₂ B) x) *
        (Adelic.Evaluation.finiteSchwartzFunction F 6 f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) *
          Adelic.DataTheta.gaussianValue (B.period z).matrix ((B.frame z).invᵀ.mulVec u)
            (fun i => (B.rationalPosition x i : ℝ))) := by ring
      _ = _ := by rw [quadraticPhase_neg_mul, one_mul]
  unfold IntrinsicSplitTensor.Intrinsic.splitKernel IntrinsicBlockCompletion.IntrinsicKernel.literalCompleted Adelic.DataTheta.completedTheta
  rw [IntrinsicJacobiComparison.Intrinsic.native_completion_comparison B₁ B₂ B hC₁ hC₂ hC hG₁ hG₂ hG, ht]

theorem completed_kernel_comparison
    (hC₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁) (hC₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hG₁ : Adelic.DataTheta.GeometryIdentification B₁) (hG₂ : Adelic.DataTheta.GeometryIdentification B₂)
    (hG : Adelic.DataTheta.GeometryIdentification B) (f : Adelic.FiniteSchwartz.finiteSchwartz F 6) :
    ∃ g : Adelic.FiniteSchwartz.finiteSchwartz F 6,
      (∀ x : Fin 6 → F, Adelic.Evaluation.finiteSchwartzFunction F 6 g (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x) =
        IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F 6 (-IntrinsicPositionMatrices.IntrinsicShearComparison.shearBilinear B₁ B₂ B) x *
          Adelic.Evaluation.finiteSchwartzFunction F 6 f (Weil.AdelicSplitting.FiniteCosets.Construction.finiteRationalPosition x)) ∧
      ∀ z u, IntrinsicSplitTensor.Intrinsic.splitKernel B₁ B₂ g z (IntrinsicSplitTensor.Intrinsic.splitJacobi B₁ B₂ z u) =
        Adelic.DataTheta.completedTheta B f (B.period z).matrix ((B.frame z).invᵀ.mulVec u) := by
  obtain ⟨g,hg⟩ := IntrinsicQuadraticPhase.Intrinsic.native_quadratic_phase_input F 6 f (-IntrinsicPositionMatrices.IntrinsicShearComparison.shearBilinear B₁ B₂ B)
  exact ⟨g,hg,completed_kernel_comparison_of_weights B₁ B₂ B hC₁ hC₂ hC hG₁ hG₂ hG f g hg⟩

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicComparison.IntrinsicKernel
