import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumModel
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComparisonRationalTensor

/-! # Intrinsic Kernel Sum Trace -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumTrace.CM

noncomputable section

/-! The ThetaKernel orthogonal sum has exactly the original rational trace
pairing. Any fully identified native comparison therefore supplies a
fixed rational symplectic coordinate system for the source tensor space. -/

open scoped Classical _root_.NumberField
open _root_.NumberField
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)
  (β : K) (hβ : IsCMField.complexConj K β = β) (hβ0 : β ≠ 0)
  (a : Fin 2 → K) (ha : ∀ j, IsCMField.complexConj K (a j) = a j) (ha0 : ∀ j, a j ≠ 0)

theorem source_sum_tensor_trace (x y : TransportNew.CM.TensorPositions K) :
    Algebra.trace ℚ (maximalRealSubfield K)
      (RepresentationTheory.Weil.AdelicSplitting.TensorSpace.Construction.tracePairing (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 3 2
        (CMGlobalFrames.CM.cmHermitianUnit K δ hδ β hβ hβ0).val
        (RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic.blockUnit (SingleLineArithmetic.CM.directSingleLineSkewUnit K δ hδ hδ0 (a 0) (ha 0) (ha0 0))
          (SingleLineArithmetic.CM.directSingleLineSkewUnit K δ hδ hδ0 (a 1) (ha 1) (ha0 1))).val
        (QuadraticTensor.CM.quadraticTensorPosition K δ hδ hδ0 x) (QuadraticTensor.CM.quadraticTensorPosition K δ hδ hδ0 y)) =
      -Algebra.trace ℚ K (δ * TransportNew.CM.tensorHermitian K β a x y) := by
  rw [IntrinsicKernelSumModel.CM.direct_source_sum_skew_unit]
  exact IntrinsicCoordinates.CM.direct_source_tensor_trace K δ hδ hδ0 β hβ hβ0 a ha ha0 x y

variable (A : RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 2
  (CMGlobalFrames.CM.cmHermitianUnit K δ hδ β hβ hβ0)
  (RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic.blockUnit (SingleLineArithmetic.CM.directSingleLineSkewUnit K δ hδ hδ0 (a 0) (ha 0) (ha0 0))
    (SingleLineArithmetic.CM.directSingleLineSkewUnit K δ hδ hδ0 (a 1) (ha 1) (ha0 1))))
  (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 3 2
    (CMGlobalFrames.CM.cmHermitianUnit K δ hδ β hβ hβ0)
    (RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic.blockUnit (SingleLineArithmetic.CM.directSingleLineSkewUnit K δ hδ hδ0 (a 0) (ha 0) (ha0 0))
      (SingleLineArithmetic.CM.directSingleLineSkewUnit K δ hδ hδ0 (a 1) (ha 1) (ha0 1))))
  (C : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData _ _ _ A) (hC : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification C P)

def sourceSumRationalCoordinates :
    TransportNew.CM.TensorPositions K ≃ₗ[ℚ] ((RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A ⊕ RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex A) → ℚ) :=
  (IntrinsicCoordinates.CM.directSourceTensorEquiv K δ hδ hδ0).trans (ComparisonRationalTensor.CM.comparisonTensorCoordinates A P C)

include hC in
theorem source_sum_rational_coordinates_pairing (x y : TransportNew.CM.TensorPositions K) :
    RepresentationTheory.Theta.Adelic.DataTheta.standardPairing (sourceSumRationalCoordinates K δ hδ hδ0 β hβ hβ0 a ha ha0 A P C x)
      (sourceSumRationalCoordinates K δ hδ hδ0 β hβ hβ0 a ha ha0 A P C y) =
        Algebra.trace ℚ K (δ * TransportNew.CM.tensorHermitian K β a x y) := by
  change RepresentationTheory.Theta.Adelic.DataTheta.standardPairing (ComparisonRationalTensor.CM.comparisonTensorCoordinates A P C (QuadraticTensor.CM.quadraticTensorPosition K δ hδ hδ0 x))
    (ComparisonRationalTensor.CM.comparisonTensorCoordinates A P C (QuadraticTensor.CM.quadraticTensorPosition K δ hδ hδ0 y)) = _
  rw [ComparisonRationalTensor.CM.comparison_tensor_coordinates_pairing A P C hC, source_sum_tensor_trace, neg_neg]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumTrace.CM
