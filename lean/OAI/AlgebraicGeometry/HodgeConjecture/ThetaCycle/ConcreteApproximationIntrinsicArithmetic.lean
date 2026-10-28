import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoefficientIntrinsicArithmetic
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.QuadraticMultiplicityBasis
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PeriodTotal
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicComparison

/-! # Concrete Approximation Intrinsic Arithmetic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationIntrinsicArithmetic.CM

noncomputable section

/-! Every actual rational splitting approximation is realized on the
original quadratic tensor space. Its global rational frame, position
coordinates, finite input, and ball action stay fixed. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.GeometricGroup
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
  (hid : ∀ i, (v i).val 1 = true)

theorem setup_delta_imaginary : IsCMField.complexConj K D.pair.delta = -D.pair.delta :=
  D.pair.delta_imaginary

theorem setup_delta_ne_zero : D.pair.delta ≠ 0 := D.pair.delta_ne_zero

theorem setup_ball_fixed : IsCMField.complexConj K D.ball.b = D.ball.b := D.ball.conjugate_b

theorem setup_ball_nonzero : D.ball.b ≠ 0 := BallArithmetic.CM.direct_source_ball_b_ne_zero K D.ball

theorem setup_a_fixed : ∀ j, IsCMField.complexConj K (D.pair.a j) = D.pair.a j :=
  BallArithmetic.CM.direct_source_a_fixed K D.pair

theorem setup_a_nonzero : ∀ j, D.pair.a j ≠ 0 := BallArithmetic.CM.direct_source_a_ne_zero K D.pair

include hid in
theorem initial_native_active_signs :
    ∀ j, FourSplittings.CM.initialThetaSigns K v j (D.places.representative D.places.distinguished) = true := by
  intro j
  fin_cases j <;> simp [FourSplittings.CM.initialThetaSigns, FourSplittings.CM.thetaSign, D.places.identity, hid]

include hid in
theorem approximation_native_active_signs :
    ∀ j, FourSplittings.CM.newThetaSigns K v j (D.places.representative D.places.distinguished) = true := by
  intro j
  fin_cases j <;> simp [FourSplittings.CM.newThetaSigns, FourSplittings.CM.thetaSign, D.places.identity, hid]

abbrev approximationNativeCoefficients := QuadraticMultiplicityBasis.CM.basisMultiplicityCoefficients K D.pair.a A.basis

theorem approximation_native_coefficients_fixed :
    ∀ j, IsCMField.complexConj K (approximationNativeCoefficients K D A j) =
      approximationNativeCoefficients K D A j :=
  fun j => TransportNew.CM.multiplicity_norm_fixed K D.pair.a (setup_a_fixed K D) (A.basis j)

theorem approximation_native_coefficients_nonzero :
    ∀ j, approximationNativeCoefficients K D A j ≠ 0 := A.nondegenerate

theorem approximation_native_coefficient_signs :
    ∀ j τ, if FourSplittings.CM.newThetaSigns K v j (D.places.representative τ) = true
      then (HeckeCycles.ReferenceDatum.CM.embeddings K D.places τ (D.pair.delta * approximationNativeCoefficients K D A j)).im < 0
      else 0 < (HeckeCycles.ReferenceDatum.CM.embeddings K D.places τ (D.pair.delta * approximationNativeCoefficients K D A j)).im := by
  intro j τ
  have ht := A.coefficient_signs j τ
  have hr := CMArchimedeanCoordinates.CM.source_imaginary_real_zero K D.places D.pair.delta (setup_delta_imaginary K D) τ
  rw [map_mul, Complex.mul_im, hr, zero_mul, zero_add]
  cases hd : FourSplittings.CM.newThetaSigns K v j (D.places.representative τ) <;>
    simp [hd, ComplexMultiplication.SignSwitch.CM.signValue] at ht ⊢ <;> nlinarith

abbrev approximationCoefficientArithmetic :
    RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K D.pair.delta (setup_delta_imaginary K D)) 2
      (CMGlobalFrames.CM.cmHermitianUnit K D.pair.delta (setup_delta_imaginary K D) D.ball.b (setup_ball_fixed K D)
        (setup_ball_nonzero K D))
      (BallArithmetic.CM.directSourceSkewUnit K D.pair.delta (setup_delta_imaginary K D) (setup_delta_ne_zero K D)
        (approximationNativeCoefficients K D A) (approximation_native_coefficients_fixed K D A)
        (approximation_native_coefficients_nonzero K D A)) :=
  CoefficientIntrinsicArithmetic.CM.sourceCoefficientArithmetic K D.ball D.places D.pair.delta (setup_delta_imaginary K D) (setup_delta_ne_zero K D)
    (approximationNativeCoefficients K D A) (approximation_native_coefficients_fixed K D A)
    (approximation_native_coefficients_nonzero K D A)
    (fun j τ => FourSplittings.CM.newThetaSigns K v j (D.places.representative τ))
    (approximation_native_active_signs K D hid) (approximation_native_coefficient_signs K D A)

def approximationFixedArithmetic :
    RepresentationTheory.Theta.Adelic.BallGeometryData.BallArithmeticData (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K D.pair.delta (setup_delta_imaginary K D)) 2
      (CMGlobalFrames.CM.cmHermitianUnit K D.pair.delta (setup_delta_imaginary K D) D.ball.b (setup_ball_fixed K D)
        (setup_ball_nonzero K D))
      (BallArithmetic.CM.directSourceSkewUnit K D.pair.delta (setup_delta_imaginary K D) (setup_delta_ne_zero K D) D.pair.a
        (setup_a_fixed K D) (setup_a_nonzero K D)) :=
  MultiplicityArithmeticTransport.CM.transportMultiplicityArithmetic (approximationCoefficientArithmetic K D A hid)
    (QuadraticMultiplicityBasis.CM.quadraticMultiplicityBasis K D.pair.delta (setup_delta_imaginary K D) (setup_delta_ne_zero K D) A.basis)
    (QuadraticMultiplicityBasis.CM.quadratic_multiplicity_basis_congruence K D.pair.delta (setup_delta_imaginary K D) (setup_delta_ne_zero K D)
      D.pair.a (setup_a_fixed K D) (setup_a_nonzero K D) A.basis A.orthogonal
      (approximation_native_coefficients_fixed K D A) (approximation_native_coefficients_nonzero K D A))

abbrev approximationFixedComparison :=
  @RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison (maximalRealSubfield K) _ (BallArithmetic.CM.directNativeRealNumberField K)
    (QuadraticModel.CM.cmQuadraticParameter K D.pair.delta (setup_delta_imaginary K D)) 2
    (CMGlobalFrames.CM.cmHermitianUnit K D.pair.delta (setup_delta_imaginary K D) D.ball.b (setup_ball_fixed K D)
      (setup_ball_nonzero K D))
    (BallArithmetic.CM.directSourceSkewUnit K D.pair.delta (setup_delta_imaginary K D) (setup_delta_ne_zero K D) D.pair.a
      (setup_a_fixed K D) (setup_a_nonzero K D))
    (approximationFixedArithmetic K D A hid) (SourceComponents.CM.directSourceFrames K D.pair)

theorem approximation_fixed_native_input
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (Fin D.places.count × (Fin 3 × Fin 2))) :
    IntrinsicReference.CM.nativeOriginalFiniteInput (approximationFixedArithmetic K D A hid) φ =
      IntrinsicReference.CM.nativeOriginalFiniteInput (BallArithmetic.CM.directSourceBallArithmeticData K D.pair
        (initial_native_active_signs K D hid) D.ball.other_place) φ := rfl

theorem approximation_fixed_native_ball_action :
    RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom (approximationFixedArithmetic K D A hid) =
      RepresentationTheory.Theta.Adelic.GeometricGroup.geometricBallHom (BallArithmetic.CM.directSourceBallArithmeticData K D.pair
        (initial_native_active_signs K D hid) D.ball.other_place) := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationIntrinsicArithmetic.CM
