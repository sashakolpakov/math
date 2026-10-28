import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumModel
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComparisonRationalTensor

/-! # Intrinsic Kernel Sum Components -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumComponents.CM

noncomputable section

/-! Actual CM tensor and geometric-frame coordinates for the native
ThetaKernel orthogonal sum, compared with the original source embeddings. -/

open scoped Classical _root_.NumberField Kronecker
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true)

theorem native_c38_sum_normalizer (v : Fin places.count) :
    IntrinsicTensorComplexCoordinates.CM.nativeTensorComponentNormalizer (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ) v =
      IntrinsicTensorComplexCoordinates.CM.nativeTensorComponentNormalizer (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ B.other_place) v := by
  unfold IntrinsicTensorComplexCoordinates.CM.nativeTensorComponentNormalizer
  rw [IntrinsicKernelSumModel.CM.native_c38_sum_basis]
  rfl

theorem native_c38_sum_paired_components
    (w : Fin places.count → ((Fin 3 × Fin 2 → ℂ) × (Fin 3 × Fin 2 → ℂ))) :
    IntrinsicTensorComplexCoordinates.CM.nativePairedTensorComponents (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ) w =
      IntrinsicTensorComplexCoordinates.CM.nativePairedTensorComponents (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ B.other_place) w := by
  refine funext (fun v : Fin places.count => ?_)
  apply Prod.ext
  · exact congrArg (fun M : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ => M.mulVec (w v).1)
      (native_c38_sum_normalizer K Q hμ v)
  · funext ij
    exact congrArg₂ (fun (b : Bool) (M : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) =>
      (if v = places.distinguished ∧ ij.1 = 2 then (-1 : ℂ) else 1) *
        (if b then (1 : ℂ) else -1) * (M.map star).mulVec (w v).2 ij)
      (IntrinsicKernelSumModel.CM.native_c38_sum_positive K Q hμ v ij.2) (native_c38_sum_normalizer K Q hμ v)

theorem native_c38_sum_rational_components (x : TransportNew.CM.TensorPositions K) :
    RepresentationTheory.Theta.Adelic.BallGeometryData.realTensorComponents (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ)
      (fun v j => RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (maximalRealSubfield K)
        (QuadraticModel.CM.cmQuadraticParameter K Q.delta Q.delta_imaginary) (.inl (RealPlaces.CM.sourceRealPlaces K places v))
        (QuadraticTensor.CM.quadraticTensorPosition K Q.delta Q.delta_imaginary Q.delta_ne_zero x j)) =
      SourceComponents.CM.directSourceComplexComponents K Q hμ B.other_place (ComplexTransition.CM.totalEmbedding K x) := by
  have h := native_c38_sum_paired_components K Q hμ
    (SourceComponents.CM.sourcePairedTensorCoordinates K places (ComplexTransition.CM.totalEmbedding K x))
  refine Eq.trans ?_ h
  rw [SourceComponents.CM.source_paired_tensor_embedding]
  apply IntrinsicTensorComplexCoordinates.CM.native_real_tensor_components_of_values
  intro v j
  exact (CMArchimedeanCoordinates.CM.source_complex_coordinate_rational K places Q.delta Q.delta_imaginary Q.delta_ne_zero v
    (QuadraticTensor.CM.quadraticTensorPosition K Q.delta Q.delta_imaginary Q.delta_ne_zero x j)).trans
    (congrArg (HeckeCycles.ReferenceDatum.CM.embeddings K places v)
      ((QuadraticModel.CM.cmQuadraticEquiv K Q.delta Q.delta_imaginary Q.delta_ne_zero).apply_symm_apply _))

variable (C : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData _ _ _ (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ))
  (hC : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification C (IntrinsicKernelArithmetic.CM.directSourceNativeSumFrames K Q))

include hC in
theorem native_c38_sum_complex_phase_rational (x : TransportNew.CM.TensorPositions K) :
    C.complexPhase (fun i => (C.rationalPhase
      ((IntrinsicKernelArithmetic.CM.directSourceNativeSumFrames K Q).rational.coordinates
        (QuadraticTensor.CM.quadraticTensorPosition K Q.delta Q.delta_imaginary Q.delta_ne_zero x)) i : ℂ)) =
      SourceComponents.CM.directSourceComplexComponents K Q hμ B.other_place (ComplexTransition.CM.totalEmbedding K x) :=
  (ComparisonRationalTensor.CM.comparison_complex_phase_rational_tensor (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ)
    (IntrinsicKernelArithmetic.CM.directSourceNativeSumFrames K Q) C hC
    (QuadraticTensor.CM.quadraticTensorPosition K Q.delta Q.delta_imaginary Q.delta_ne_zero x)).trans
    (native_c38_sum_rational_components K Q hμ x)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumComponents.CM
