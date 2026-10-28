import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationPeriodGraph
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationLevel
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicComparison

/-! # Concrete Approximation Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationComparison.CM

noncomputable section

/-! The same original finite input realizes every actual approximation
in the native theta model. The identities retain all Jacobi parameters
and every unprojected Taylor order in the original source coordinates. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
  (hid : ∀ i, (v i).val 1 = true)

theorem approximation_original_input_eq (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K D.places)) :
    IntrinsicReference.CM.nativeOriginalFiniteInput (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid)
      (ReindexTheta.CM.finiteInputReindex (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places)
        (IndexedCovariance.CM.indexedFiniteOscillatorInput (ConcreteApproximationPeriodGraph.CM.originalNativeSymplecticTransition K D hid) φ)) =
      ConcreteApproximationLevel.CM.initialNativeInput K D hid φ :=
  ConcreteApproximationIntrinsicArithmetic.CM.approximation_fixed_native_input K D A hid _

theorem approximation_original_completed_theta (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K D.places))
    (z : D.ball.Domain) (ξ : PeriodTotal.CM.TotalPositions K D.places → ℂ) :
    let γ := ConcreteApproximationPeriodGraph.CM.originalNativeSymplecticTransition K D hid
    let Z := MovingTotalPeriod.CM.approximationTotalPeriod K D A z.val
    RepresentationTheory.Theta.Adelic.DataTheta.completedTheta (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid) (ConcreteApproximationLevel.CM.initialNativeInput K D hid φ)
      ((ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid).period (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)).matrix
      (fun i => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z ξ ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places).symm i)) =
      IndexedCovariance.CM.indexedThetaMultiplier γ Z * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z ξ := by
  let γ := ConcreteApproximationPeriodGraph.CM.originalNativeSymplecticTransition K D hid
  let Z := MovingTotalPeriod.CM.approximationTotalPeriod K D A z.val
  let W := (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid).period (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)
  let ξ' := fun i => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z ξ ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places).symm i)
  let Ψ := IndexedCovariance.CM.indexedFiniteOscillatorInput γ φ
  have hi := congrArg (fun f => RepresentationTheory.Theta.Adelic.DataTheta.completedTheta (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid) f W.matrix ξ')
    (approximation_original_input_eq K D A hid φ).symm
  have hn := IntrinsicReference.CM.native_original_completed_theta (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid) (SourceComponents.CM.directSourceFrames K D.pair)
    (ReindexTheta.CM.finiteInputReindex (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places) Ψ) W ξ'
  have hr := SourceIntrinsicComparison.CM.completed_reindex_from_target (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places) Ψ W
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z ξ)
  have hp := congrArg (fun U => RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed Ψ U ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z ξ))
    (ConcreteApproximationPeriodGraph.CM.approximation_native_period_transform K D A hid z)
  have hc := IndexedCovariance.CM.indexed_completed_theta_covariance γ φ Z ξ
  exact hi.trans (hn.trans (hr.trans (hp.trans hc)))

theorem approximation_original_completed_theta_jets (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K D.places))
    (z : D.ball.Domain) (a : ℕ) (u : Fin a → PeriodTotal.CM.TotalPositions K D.places → ℂ) :
    let γ := ConcreteApproximationPeriodGraph.CM.originalNativeSymplecticTransition K D hid
    let Z := MovingTotalPeriod.CM.approximationTotalPeriod K D A z.val
    iteratedFDeriv ℂ a
      (RepresentationTheory.Theta.Adelic.DataTheta.completedTheta (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid) (ConcreteApproximationLevel.CM.initialNativeInput K D hid φ)
        ((ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid).period (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)).matrix) 0
      (fun j i => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z (u j) ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places).symm i)) =
      IndexedCovariance.CM.indexedThetaMultiplier γ Z * iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z) 0 u := by
  let γ := ConcreteApproximationPeriodGraph.CM.originalNativeSymplecticTransition K D hid
  let Z := MovingTotalPeriod.CM.approximationTotalPeriod K D A z.val
  let W := (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid).period (SourceIntrinsicBall.CM.sourceNativeBallPoint K D.ball z)
  let u' := fun j => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z (u j)
  let Ψ := IndexedCovariance.CM.indexedFiniteOscillatorInput γ φ
  have hi := congrArg (fun f => iteratedFDeriv ℂ a
    (RepresentationTheory.Theta.Adelic.DataTheta.completedTheta (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedComparison K D A hid) f W.matrix) 0
      (fun j i => u' j ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places).symm i)))
    (approximation_original_input_eq K D A hid φ).symm
  have hn := SourceIntrinsicComparison.CM.native_original_completed_theta_jets (ConcreteApproximationIntrinsicArithmetic.CM.approximationFixedArithmetic K D A hid)
    (SourceComponents.CM.directSourceFrames K D.pair) (ReindexTheta.CM.finiteInputReindex (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places) Ψ) W a
    (fun j i => u' j ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places).symm i))
  have hr := SourceIntrinsicComparison.CM.reindexed_completed_theta_jets (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K D.places) Ψ W a u'
  have hp := congrArg (fun U => iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed Ψ U) 0 u')
    (ConcreteApproximationPeriodGraph.CM.approximation_native_period_transform K D A hid z)
  have hc := IndexedCovariance.CM.indexed_completed_jet_covariance γ φ Z a u
  exact hi.trans (hn.trans (hr.trans (hp.trans hc)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationComparison.CM
