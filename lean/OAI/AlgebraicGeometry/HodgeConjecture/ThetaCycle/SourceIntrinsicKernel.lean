import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernel
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelArithmetic
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalLevel

/-! # Source Intrinsic Kernel -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicKernel.CM

noncomputable section

/-! Apply the complete checked native ThetaKernel theorem to the actual source
two-line arithmetic. All comparison witnesses and every native conclusion
are retained; complete AdelicTheta is the sole remaining native prerequisite. -/

open scoped Classical _root_.NumberField _root_.Matrix _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.Data
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicGlobal OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompletionData.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicPrerequisites.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicOne.Intrinsic

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

theorem nativeFullTensorDecompositionInput : RepresentationTheory.Theta.DerivativeFactorizationPrerequisites.Prerequisites.TensorDecomposition.Statement :=
  ⟨Analysis.Schwartz.TensorDecomposition.Constructions.finite_product_decomposition, Analysis.Schwartz.TensorDecomposition.Constructions.finite_local_factorization⟩

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true)

theorem source_c38_quadratic_condition :
    QuadraticModel.CM.cmQuadraticParameter K Q.delta Q.delta_imaginary ≠ 0 ∧
      ¬ IsSquare (QuadraticModel.CM.cmQuadraticParameter K Q.delta Q.delta_imaginary) :=
  ⟨QuadraticModel.CM.cm_quadratic_parameter_ne_zero K Q.delta Q.delta_imaginary Q.delta_ne_zero,
    QuadraticModel.CM.cm_quadratic_parameter_not_isSquare K Q.delta Q.delta_imaginary Q.delta_ne_zero⟩

theorem source_c38_standard_character :
    RepresentationTheory.Theta.Adelic.DataTheta.Descent.StandardArchCharacter (A := SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ 0)
      (FieldAdelicCharacter.CM.fieldAdelicCharacter (maximalRealSubfield K)) := by
  intro v t
  exact RealCharacterNormalization.CM.field_adelic_character_standard_real_coordinate (maximalRealSubfield K)
    (RealPlaces.CM.sourceRealPlaces K places v) (CMArchimedeanCoordinates.CM.sourceRealCoordinate K places v) t

structure SourceNativeThetaKernelData where
  first : RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands.SummandWitnesses
    (SingleLineArithmetic.CM.directSingleLineSkewUnit K Q.delta Q.delta_imaginary Q.delta_ne_zero (Q.a 0)
      (BallArithmetic.CM.direct_source_a_fixed K Q 0) (BallArithmetic.CM.direct_source_a_ne_zero K Q 0))
    (source_c38_quadratic_condition K Q).1 (SingleLineComponents.CM.directSingleLineFrames K Q 0) (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ 0)
  second : RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands.SummandWitnesses (IntrinsicKernelArithmetic.CM.directSourceSecondLine K Q hμ).form
    (source_c38_quadratic_condition K Q).1 (SingleLineComponents.CM.directSingleLineFrames K Q 1)
    (RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands.secondArithmetic (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ 0) (IntrinsicKernelArithmetic.CM.directSourceSecondLine K Q hμ))
  total : RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic.TotalWitnesses (source_c38_quadratic_condition K Q).1
    (IntrinsicKernelArithmetic.CM.directSourceNativeSumFrames K Q) (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ)
  compact : ∀ p : RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic.CompactFrameChoice (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ),
    RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic.TotalWitnesses (source_c38_quadratic_condition K Q).1 (IntrinsicKernelArithmetic.CM.directSourceNativeSumFrames K Q)
      (RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic.choiceArithmetic (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ) p)
  first_valid : RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands.SummandValid first (FieldAdelicCharacter.CM.fieldAdelicCharacter (maximalRealSubfield K))
  second_valid : RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands.SummandValid second (FieldAdelicCharacter.CM.fieldAdelicCharacter (maximalRealSubfield K))
  total_valid : RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic.TotalValid total (FieldAdelicCharacter.CM.fieldAdelicCharacter (maximalRealSubfield K))
  compact_valid : ∀ p, RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic.TotalValid (compact p) (FieldAdelicCharacter.CM.fieldAdelicCharacter (maximalRealSubfield K))
  conclusion : RepresentationTheory.Theta.Kernel.IntrinsicCompletionData.Intrinsic.NativeConclusion first second total compact (FieldAdelicCharacter.CM.fieldAdelicCharacter (maximalRealSubfield K))
    total_valid compact_valid (IntrinsicAnalysis.CM.nativeGaussianConvergenceInput (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ)))

theorem exists_source_native_c38_data (hAdelicTheta : RepresentationTheory.Theta.Adelic.Data.CompleteStatement) :
    Nonempty (SourceNativeThetaKernelData K Q hμ) := by
  have h := IntrinsicKernel.CM.nativeThetaKernelFullInput RepresentationTheory.Theta.Kernel.IntrinsicPrerequisites.Intrinsic.full_CotangentBundle RepresentationTheory.Theta.Kernel.IntrinsicPrerequisites.Intrinsic.full_DerivativeFactorization nativeFullTensorDecompositionInput RepresentationTheory.Theta.Kernel.IntrinsicOne.Intrinsic.full_native_ThetaOneForms hAdelicTheta
    (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K Q.delta Q.delta_imaginary)
    (source_c38_quadratic_condition K Q)
    (CMGlobalFrames.CM.cmHermitianUnit K Q.delta Q.delta_imaginary B.b B.conjugate_b (BallArithmetic.CM.direct_source_ball_b_ne_zero K B))
    (SingleLineArithmetic.CM.directSingleLineSkewUnit K Q.delta Q.delta_imaginary Q.delta_ne_zero (Q.a 0)
      (BallArithmetic.CM.direct_source_a_fixed K Q 0) (BallArithmetic.CM.direct_source_a_ne_zero K Q 0))
    (PrincipalLevel.CM.native_ball_hermitian_unit_conjugate_transpose K Q.delta Q.delta_imaginary B)
    (SingleLineArithmetic.CM.direct_single_line_skew_conjugate_transpose K Q.delta Q.delta_imaginary Q.delta_ne_zero (Q.a 0)
      (BallArithmetic.CM.direct_source_a_fixed K Q 0) (BallArithmetic.CM.direct_source_a_ne_zero K Q 0))
    (FieldAdelicCharacter.CM.fieldAdelicCharacter (maximalRealSubfield K))
    (FieldAdelicCharacter.CM.field_adelic_character_continuous (maximalRealSubfield K))
    (FieldAdelicCharacter.CM.field_adelic_character_unitary (maximalRealSubfield K))
    (FieldAdelicCharacter.CM.field_adelic_character_nontrivial (maximalRealSubfield K))
    (FieldAdelicCharacter.CM.field_adelic_character_principal (maximalRealSubfield K))
    (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ 0) (IntrinsicKernelArithmetic.CM.directSourceSecondLine K Q hμ)
    (SingleLineComponents.CM.directSingleLineFrames K Q 0) (SingleLineComponents.CM.directSingleLineFrames K Q 1)
    (source_c38_standard_character K Q hμ) (IntrinsicAnalysis.CM.nativeGaussianConvergenceInput _) (IntrinsicAnalysis.CM.nativeGaussianConvergenceInput _) (IntrinsicAnalysis.CM.nativeGaussianConvergenceInput _)
  obtain ⟨Q₁, Q₂, Q₀, Qc, h₁, h₂, h₀, hQc, hconclusion⟩ := h
  exact ⟨⟨Q₁, Q₂, Q₀, Qc, h₁, h₂, h₀, hQc, hconclusion⟩⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicKernel.CM
