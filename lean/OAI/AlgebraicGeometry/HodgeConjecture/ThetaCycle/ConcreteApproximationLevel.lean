import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationIntrinsicArithmetic
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalGeometricLevel
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicLine

/-! # Concrete Approximation Level -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationLevel.CM

noncomputable section

/-! A single principal level for the one original total finite input
and all actual rational approximations, with the literal source ball
action and projective denominator in the full tensor law. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) (hid : ∀ i, (v i).val 1 = true)

def initialNativeInput (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K D.places)) :
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (maximalRealSubfield K) (3 * 2) :=
  SourceIntrinsicComparison.CM.directSourceNativeFiniteInput K D.pair (ConcreteApproximationIntrinsicArithmetic.CM.initial_native_active_signs K D hid) D.ball.other_place
    (fun j => (D.initialPeriods j).coordinates) D.initial_coefficients φ

abbrev setupArchimedeanElement (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : D.ball.principalLevel N g) :=
  RepresentationTheory.Theta.Adelic.RationalSU.rationalArchimedeanSU (maximalRealSubfield K)
    (CMGlobalFrames.CM.cmHermitianUnit K D.pair.delta D.pair.delta_imaginary D.ball.b D.ball.conjugate_b
      (BallArithmetic.CM.direct_source_ball_b_ne_zero K D.ball))
    (RationalBallUnitary.CM.rationalBallSU K D.pair.delta D.pair.delta_imaginary D.pair.delta_ne_zero D.ball N g hg)

def ActualApproximationThetaCovariant (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K D.places))
    (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : D.ball.principalLevel N g) : Prop :=
  ∀ (ε : ℝ) (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
    (z : D.ball.Domain) (a : ℕ) (u : Fin a → RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) → ℂ),
    RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid) (initialNativeInput K D hid φ) a
      (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball (BallLineAction.CM.ballPrincipalAction K D.ball g hg.1 z))
      (fun i => RepresentationTheory.Theta.Adelic.BallGeometryData.dualFrameChange (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid)
        (setupArchimedeanElement K D N g hg) (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z) (u i)) =
      ((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2) ^ 2 *
        RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid) (initialNativeInput K D hid φ) a
          (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z) u

theorem native_covariance_for_actual_approximations
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K D.places)) (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
    (hg : D.ball.principalLevel N g)
    (h : IntrinsicFixedCovariance.CM.NativeGeometricThetaCovariant (SourceComponents.CM.directSourceFrames K D.pair)
      (setupArchimedeanElement K D N g hg) (initialNativeInput K D hid φ)) :
    ActualApproximationThetaCovariant K D hid φ N g hg := by
  intro ε A z a u
  have hc := h (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z) a u
  have hp := SourceIntrinsicLine.CM.source_native_principal_ball_action K D.pair (ConcreteApproximationIntrinsicArithmetic.CM.initial_native_active_signs K D hid)
    D.ball.other_place N g hg z
  have hf := SourceIntrinsicLine.CM.source_native_natural_half_factor K D.pair (ConcreteApproximationIntrinsicArithmetic.CM.initial_native_active_signs K D hid)
    D.ball.other_place N g hg z
  have he := congrArg (fun w =>
    RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid) (initialNativeInput K D hid φ) a w
      (fun i => RepresentationTheory.Theta.Adelic.BallGeometryData.dualFrameChange (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid)
        (setupArchimedeanElement K D N g hg) (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z) (u i))) hp.symm
  exact he.trans (hc.trans (congrArg (fun c => c *
    RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid) (initialNativeInput K D hid φ) a
      (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z) u) hf))

theorem exists_original_input_approximation_theta_level (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K D.places)) :
    ∃ L : ℕ, 0 < L ∧ ∀ N : ℕ, L ∣ N →
      ∀ (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : D.ball.principalLevel N g),
        IntrinsicFixedCovariance.CM.NativeGeometricThetaCovariant (SourceComponents.CM.directSourceFrames K D.pair)
          (setupArchimedeanElement K D N g hg) (initialNativeInput K D hid φ) ∧
        ActualApproximationThetaCovariant K D hid φ N g hg := by
  let f := initialNativeInput K D hid φ
  have hlevel := PrincipalGeometricLevel.CM.exists_principal_all_geometric_theta_level K D.pair.delta D.pair.delta_imaginary
    D.pair.delta_ne_zero D.ball 2 (by decide)
    (BallArithmetic.CM.directSourceSkewUnit K D.pair.delta D.pair.delta_imaginary D.pair.delta_ne_zero D.pair.a
      (BallArithmetic.CM.direct_source_a_fixed K D.pair) (BallArithmetic.CM.direct_source_a_ne_zero K D.pair))
    (QuadraticMultiplicityBasis.CM.direct_source_skew_unit_conjugate_transpose K D.pair.delta D.pair.delta_imaginary D.pair.delta_ne_zero
      D.pair.a (BallArithmetic.CM.direct_source_a_fixed K D.pair) (BallArithmetic.CM.direct_source_a_ne_zero K D.pair))
    (SourceComponents.CM.directSourceFrames K D.pair) {f}
  refine ⟨hlevel.choose, hlevel.choose_spec.1, ?_⟩
  intro N hN g hg
  have h := (hlevel.choose_spec.2 N hN).2 g hg f (Finset.mem_singleton_self f)
  exact ⟨h, native_covariance_for_actual_approximations K D hid φ N g hg h⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationLevel.CM
