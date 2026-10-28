import OAI.RepresentationTheory.Theta.Kernel.IntrinsicImaginaryComparison
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitTensor

/-! # Intrinsic Jacobi Comparison -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicJacobiComparison.Intrinsic

noncomputable section

/-! The actual inverse-transpose Jacobi frames have the expected native
coordinate relation, and their theta completion factors agree. -/

open scoped _root_.NumberField Classical _root_.Matrix BigOperators _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicGlobal OAI.RepresentationTheory.Theta.Kernel.IntrinsicHodgeSplit.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicBlockSiegel.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicComplexTransport.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement.IntrinsicPositionTransport
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionMatrices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicImaginaryComparison.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicInversePullback.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitTensor.Intrinsic

theorem inverse_transpose_pairing {I : Type} [Fintype I] [DecidableEq I]
    (a : (Matrix I I ℂ)ˣ) (x u : I → ℂ) :
    x ⬝ᵥ (a.invᵀ.mulVec u) = (a.inv.mulVec x) ⬝ᵥ u := by
  rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K₁ : (Matrix (Fin 1) (Fin 1) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 1 H K₁} {S : IntrinsicSplitting.IntrinsicSummands.SecondLine A}
variable {P₁ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H K₁} {P₂ : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 1 H S.form}
variable (B₁ : Adelic.DataTheta.ComparisonData F H K₁ A)
variable (B₂ : Adelic.DataTheta.ComparisonData F H S.form (IntrinsicSplitting.IntrinsicSummands.secondArithmetic A S))
variable (B : Adelic.DataTheta.ComparisonData F H (IntrinsicSplitting.IntrinsicArithmetic.blockUnit K₁ S.form) (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S))

theorem splitCoordinates_dot (x y : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) :
    (IntrinsicHodgeSplit.Intrinsic.splitCoordinates A S x) ⬝ᵥ (IntrinsicHodgeSplit.Intrinsic.splitCoordinates A S y) = x ⬝ᵥ y := by
  change (∑ i, x ((IntrinsicHodgeSplit.Intrinsic.frameIndex A S).symm i) * y ((IntrinsicHodgeSplit.Intrinsic.frameIndex A S).symm i)) = ∑ i, x i * y i
  exact (IntrinsicHodgeSplit.Intrinsic.frameIndex A S).symm.sum_comp (fun i => x i * y i)

theorem inverse_frame_positions
    (hC₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁) (hC₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hG₁ : Adelic.DataTheta.GeometryIdentification B₁) (hG₂ : Adelic.DataTheta.GeometryIdentification B₂)
    (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) (x : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) :
    (IntrinsicBlockSiegel.Intrinsic.blockFrame (B₁.frame z) (B₂.frame z)).inv.mulVec ((IntrinsicPositionMatrices.Intrinsic.positionMatrix B₁ B₂ B).mulVec x) =
      IntrinsicHodgeSplit.Intrinsic.splitCoordinates A S ((B.frame z).inv.mulVec x) := by
  let a := (B.frame z).inv.mulVec x
  have ha : (B.frame z).val.mulVec a = x := by
    change (B.frame z).val.mulVec ((B.frame z).inv.mulVec x) = x
    rw [Matrix.mulVec_mulVec, (B.frame z).val_inv, Matrix.one_mulVec]
  have hf := congrArg (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _)
    (IntrinsicComplexTransport.Intrinsic.complexPhaseChange_graph B₁ B₂ B hG₁ hG₂ hG z a)
  rw [IntrinsicCoordinateAgreement.IntrinsicPositionTransport.complexPhaseChange_positions B₁ B₂ B hC₁ hC₂ hC] at hf
  change IntrinsicCoordinateAgreement.IntrinsicPositionTransport.complexPositionChange B₁ B₂ B ((B.frame z).val.mulVec a) =
    (IntrinsicBlockSiegel.Intrinsic.blockFrame (B₁.frame z) (B₂.frame z)).val.mulVec (IntrinsicHodgeSplit.Intrinsic.splitCoordinates A S a) at hf
  rw [ha, ← IntrinsicPositionMatrices.Intrinsic.positionMatrix_apply B₁ B₂ B hC₁ hC₂ hC] at hf
  have hi : (IntrinsicBlockSiegel.Intrinsic.blockFrame (B₁.frame z) (B₂.frame z)).inv.mulVec
      ((IntrinsicBlockSiegel.Intrinsic.blockFrame (B₁.frame z) (B₂.frame z)).val.mulVec (IntrinsicHodgeSplit.Intrinsic.splitCoordinates A S a)) =
        IntrinsicHodgeSplit.Intrinsic.splitCoordinates A S a := by
    rw [Matrix.mulVec_mulVec, (IntrinsicBlockSiegel.Intrinsic.blockFrame (B₁.frame z) (B₂.frame z)).inv_val, Matrix.one_mulVec]
  exact (congrArg (IntrinsicBlockSiegel.Intrinsic.blockFrame (B₁.frame z) (B₂.frame z)).inv.mulVec hf).trans hi

theorem native_jacobi_relation
    (hC₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁) (hC₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hG₁ : Adelic.DataTheta.GeometryIdentification B₁) (hG₂ : Adelic.DataTheta.GeometryIdentification B₂)
    (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) (u : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) :
    (B.frame z).invᵀ.mulVec u =
      (IntrinsicPositionMatrices.Intrinsic.positionMatrix B₁ B₂ B)ᵀ.mulVec (IntrinsicSplitTensor.Intrinsic.splitJacobi B₁ B₂ z u) := by
  have hp (x : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) :
      x ⬝ᵥ ((B.frame z).invᵀ.mulVec u) =
        ((IntrinsicPositionMatrices.Intrinsic.positionMatrix B₁ B₂ B).mulVec x) ⬝ᵥ (IntrinsicSplitTensor.Intrinsic.splitJacobi B₁ B₂ z u) := by
    change x ⬝ᵥ ((B.frame z).invᵀ.mulVec u) =
      ((IntrinsicPositionMatrices.Intrinsic.positionMatrix B₁ B₂ B).mulVec x) ⬝ᵥ
        ((IntrinsicBlockSiegel.Intrinsic.blockFrame (B₁.frame z) (B₂.frame z)).invᵀ.mulVec (IntrinsicHodgeSplit.Intrinsic.splitCoordinates A S u))
    rw [inverse_transpose_pairing, inverse_transpose_pairing,
      inverse_frame_positions B₁ B₂ B hC₁ hC₂ hC hG₁ hG₂ hG, splitCoordinates_dot]
  have he (x : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) :
      x ⬝ᵥ ((B.frame z).invᵀ.mulVec u) =
        x ⬝ᵥ ((IntrinsicPositionMatrices.Intrinsic.positionMatrix B₁ B₂ B)ᵀ.mulVec (IntrinsicSplitTensor.Intrinsic.splitJacobi B₁ B₂ z u)) := by
    conv_rhs => rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm]
    exact hp x
  funext i
  simpa using he (Pi.single i 1)

theorem native_completion_comparison
    (hC₁ : Adelic.DataTheta.CoordinateIdentification B₁ P₁) (hC₂ : Adelic.DataTheta.CoordinateIdentification B₂ P₂)
    (hC : Adelic.DataTheta.CoordinateIdentification B (IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames P₁ P₂))
    (hG₁ : Adelic.DataTheta.GeometryIdentification B₁) (hG₂ : Adelic.DataTheta.GeometryIdentification B₂)
    (hG : Adelic.DataTheta.GeometryIdentification B) (z : Adelic.BallNatural.Ball) (u : Adelic.BallGeometryData.FrameIndex (IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic A S) → ℂ) :
    AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor (((Real.pi : ℂ) / 2) •
      AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear ((AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary (IntrinsicBlockSiegel.Intrinsic.blockPeriod (B₁.period z) (B₂.period z)).matrix)⁻¹))
        (IntrinsicSplitTensor.Intrinsic.splitJacobi B₁ B₂ z u) =
      AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor (((Real.pi : ℂ) / 2) •
        AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear ((AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.matrixImaginary (B.period z).matrix)⁻¹)) ((B.frame z).invᵀ.mulVec u) := by
  have h := IntrinsicInversePullback.Intrinsic.inverse_quadratic_pullback (IntrinsicPositionMatrices.Intrinsic.positionMatrix B₁ B₂ B) _ _
    (IntrinsicImaginaryComparison.Intrinsic.imaginary_inverse B₁ B₂ B hC₁ hC₂ hC hG₁ hG₂ hG z) (IntrinsicSplitTensor.Intrinsic.splitJacobi B₁ B₂ z u)
  rw [← native_jacobi_relation B₁ B₂ B hC₁ hC₂ hC hG₁ hG₂ hG] at h
  simp only [AlgebraicGeometry.ComplexMultiplication.ThetaCompletion.CM.thetaCompletionFactor, _root_.smul_apply, AlgebraicGeometry.ComplexMultiplication.SymplecticThetaCompletion.CM.complexMatrixBilinear_apply, smul_eq_mul]
  rw [h]

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicJacobiComparison.Intrinsic
