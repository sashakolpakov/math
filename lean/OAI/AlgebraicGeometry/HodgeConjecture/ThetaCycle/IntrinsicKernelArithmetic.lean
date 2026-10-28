import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineArithmetic
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineComponents
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting

/-! # Intrinsic Kernel Arithmetic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelArithmetic.CM

noncomputable section

/-! Instantiate native ThetaKernel's two arithmetic summands using the actual
source multiplicity coefficients in the original CM embeddings. The
second line has exactly the same V coordinates as the first. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicGlobal

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true)

def directSourceSecondLine : RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands.SecondLine (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ 0) where
  form := SingleLineArithmetic.CM.directSingleLineSkewUnit K Q.delta Q.delta_imaginary Q.delta_ne_zero (Q.a 1)
    (BallArithmetic.CM.direct_source_a_fixed K Q 1) (BallArithmetic.CM.direct_source_a_ne_zero K Q 1)
  skewHermitian := SingleLineArithmetic.CM.direct_single_line_skew_conjugate_transpose K Q.delta Q.delta_imaginary Q.delta_ne_zero (Q.a 1)
    (BallArithmetic.CM.direct_source_a_fixed K Q 1) (BallArithmetic.CM.direct_source_a_ne_zero K Q 1)
  basis := (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ 1).basisP
  positive := (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ 1).positive
  distinguished_sign := (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ 1).distinguished_sign
  normalized := (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ 1).formP

theorem direct_source_second_arithmetic :
    RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicSummands.secondArithmetic (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ 0) (directSourceSecondLine K Q hμ) =
      SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ 1 := rfl

def directSourceNativeSumArithmetic :=
  RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic.sumArithmetic (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ 0) (directSourceSecondLine K Q hμ)

def directSourceNativeSumFrames :=
  RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicGlobal.sumGlobalFrames (SingleLineComponents.CM.directSingleLineFrames K Q 0) (SingleLineComponents.CM.directSingleLineFrames K Q 1)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelArithmetic.CM
