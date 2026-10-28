import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineHalfRatio
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicComparison
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicReference

/-! # Single Line Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineComparison.CM

noncomputable section

section

/-! The original finite Schwartz input is transported once through the
fixed rational coordinate change. The resulting native completed theta
series agrees with the original source series throughout the ball, with
its exact constant and geometric half-frame factors. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

section FiniteInput

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true)
  (j : Fin 2) (C : HeckeCycles.GeometricSource.CM.SymplecticCoordinates K B places)
  (hC : C.a = Q.a j ∧ C.delta = Q.delta)

def directSingleNativeFiniteInput (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)) :
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (maximalRealSubfield K) (3 * 1) :=
  IntrinsicReference.CM.nativeOriginalFiniteInput (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j)
    (ReindexTheta.CM.finiteInputReindex (SingleLineFrame.CM.sourceSingleIndexEquiv K places)
      (IndexedCovariance.CM.indexedFiniteOscillatorInput (SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j C hC) φ))

end FiniteInput

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
  (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun j v => d j (places.representative v)))
  (hμ : ∀ j, d j (places.representative places.distinguished) = true)
  (j : Fin 2) (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
  (hL : L.coordinates.a = Q.a j ∧ L.coordinates.delta = Q.delta)

theorem single_source_native_multiplier_factor (z₀ z : B.Domain) :
    IndexedCovariance.CM.indexedThetaMultiplier (SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j
      L.coordinates hL)
        (L.period z.val) =
      SingleLineHalfRatio.CM.singleSourceNativeHalfRatio K d Q hμ j L hL z₀ *
        ((SingleLineComponents.CM.directSingleLineComparison K Q hμ j).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
          (L.halfDet z.val : ℂ)) := by
  have he := div_mul_cancel₀
    (IndexedCovariance.CM.indexedThetaMultiplier (SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j
      L.coordinates hL)
        (L.period z.val))
    (SingleLineHalfRatio.CM.single_source_native_half_denominator_ne_zero K d Q hμ j L z)
  exact he.symm.trans (congrArg (fun c : ℂ => c *
    ((SingleLineComponents.CM.directSingleLineComparison K Q hμ j).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
      (L.halfDet z.val : ℂ)))
    (SingleLineHalfRatio.CM.single_source_native_half_ratio_constant K d Q hμ j L hL z₀ z))

theorem single_source_native_indexed_completed_theta
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)) (z : B.Domain) (ξ : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    let γ := SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j L.coordinates hL
    let Z := L.period z.val
    RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (IndexedCovariance.CM.indexedFiniteOscillatorInput γ φ) (SingleLinePeriodGraph.CM.directSingleIndexedPeriod K Q hμ j z)
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z ξ) =
      IndexedCovariance.CM.indexedThetaMultiplier γ Z * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z ξ := by
  dsimp only
  exact (congrArg (fun W => RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed
    (IndexedCovariance.CM.indexedFiniteOscillatorInput (SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j
      L.coordinates hL) φ) W
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j
      L.coordinates hL)).jacobiChange
      (L.period z.val) ξ))
    (SingleLinePeriodGraph.CM.single_source_native_period_transform K d Q hμ j L hL z)).trans
    (IndexedCovariance.CM.indexed_completed_theta_covariance _ φ _ ξ)

theorem single_source_native_completed_theta
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)) (z : B.Domain) (ξ : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    let γ := SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j L.coordinates hL
    let Z := L.period z.val
    RepresentationTheory.Theta.Adelic.DataTheta.completedTheta (SingleLineComponents.CM.directSingleLineComparison K Q hμ j)
      (directSingleNativeFiniteInput K Q hμ j L.coordinates hL φ)
      ((SingleLineComponents.CM.directSingleLineComparison K Q hμ j).period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).matrix
      (fun i => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z ξ ((SingleLineFrame.CM.sourceSingleIndexEquiv K places).symm i)) =
      IndexedCovariance.CM.indexedThetaMultiplier γ Z * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z ξ := by
  dsimp only
  have hn := IntrinsicReference.CM.native_original_completed_theta (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j)
    (SingleLineComponents.CM.directSingleLineFrames K Q j)
    (ReindexTheta.CM.finiteInputReindex (SingleLineFrame.CM.sourceSingleIndexEquiv K places)
      (IndexedCovariance.CM.indexedFiniteOscillatorInput (SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j
        L.coordinates hL) φ))
    ((SingleLineComponents.CM.directSingleLineComparison K Q hμ j).period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z))
    (fun i => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j
      L.coordinates hL)).jacobiChange
        (L.period z.val) ξ ((SingleLineFrame.CM.sourceSingleIndexEquiv K places).symm i))
  have he := SourceIntrinsicComparison.CM.completed_reindex_from_target (SingleLineFrame.CM.sourceSingleIndexEquiv K places)
    (IndexedCovariance.CM.indexedFiniteOscillatorInput (SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j
      L.coordinates hL) φ)
    ((SingleLineComponents.CM.directSingleLineComparison K Q hμ j).period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z))
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j
      L.coordinates hL)).jacobiChange
        (L.period z.val) ξ)
  exact hn.trans (he.trans (single_source_native_indexed_completed_theta K d Q hμ j L hL φ z ξ))

theorem single_source_native_completed_theta_normalized
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)) (z₀ z : B.Domain) (ξ : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    let γ := SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j L.coordinates hL
    let Z := L.period z.val
    RepresentationTheory.Theta.Adelic.DataTheta.completedTheta (SingleLineComponents.CM.directSingleLineComparison K Q hμ j)
      (directSingleNativeFiniteInput K Q hμ j L.coordinates hL φ)
      ((SingleLineComponents.CM.directSingleLineComparison K Q hμ j).period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).matrix
      (fun i => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z ξ ((SingleLineFrame.CM.sourceSingleIndexEquiv K places).symm i)) =
      SingleLineHalfRatio.CM.singleSourceNativeHalfRatio K d Q hμ j L hL z₀ *
        ((SingleLineComponents.CM.directSingleLineComparison K Q hμ j).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
          (L.halfDet z.val : ℂ)) * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z ξ := by
  dsimp only
  exact (single_source_native_completed_theta K d Q hμ j L hL φ z ξ).trans
    (congrArg (fun c => c * RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ
      (L.period z.val) ξ)
      (single_source_native_multiplier_factor K d Q hμ j L hL z₀ z))

end

/-! All Taylor tensors of the retained source input agree with the
native tensors through the exact Jacobi coordinate map. No projection
or selected Taylor coefficient is used in this comparison. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
  (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun j v => d j (places.representative v)))
  (hμ : ∀ j, d j (places.representative places.distinguished) = true)
  (j : Fin 2) (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
  (hL : L.coordinates.a = Q.a j ∧ L.coordinates.delta = Q.delta)

theorem single_source_native_completed_theta_jets
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)) (z : B.Domain) (a : ℕ)
    (v : Fin a → HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    let γ := SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j L.coordinates hL
    let Z := L.period z.val
    iteratedFDeriv ℂ a
      (RepresentationTheory.Theta.Adelic.DataTheta.completedTheta (SingleLineComponents.CM.directSingleLineComparison K Q hμ j)
        (directSingleNativeFiniteInput K Q hμ j L.coordinates hL φ)
        ((SingleLineComponents.CM.directSingleLineComparison K Q hμ j).period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).matrix) 0
      (fun i j => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z (v i) ((SingleLineFrame.CM.sourceSingleIndexEquiv K places).symm j)) =
      IndexedCovariance.CM.indexedThetaMultiplier γ Z * iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z) 0 v := by
  let γ := SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j L.coordinates hL
  let Z := L.period z.val
  let Ψ := IndexedCovariance.CM.indexedFiniteOscillatorInput γ φ
  let W := (SingleLineComponents.CM.directSingleLineComparison K Q hμ j).period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
  let v' := fun i => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z (v i)
  have hn := SourceIntrinsicComparison.CM.native_original_completed_theta_jets (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j)
    (SingleLineComponents.CM.directSingleLineFrames K Q j) (ReindexTheta.CM.finiteInputReindex (SingleLineFrame.CM.sourceSingleIndexEquiv K places) Ψ) W a
    (fun i j => v' i ((SingleLineFrame.CM.sourceSingleIndexEquiv K places).symm j))
  have hr := SourceIntrinsicComparison.CM.reindexed_completed_theta_jets (SingleLineFrame.CM.sourceSingleIndexEquiv K places) Ψ W a v'
  have hp := congrArg (fun U => iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed Ψ U) 0 v')
    (SingleLinePeriodGraph.CM.single_source_native_period_transform K d Q hμ j L hL z)
  have hi := IndexedCovariance.CM.indexed_completed_jet_covariance γ φ Z a v
  exact hn.trans (hr.trans (hp.trans hi))

theorem single_source_native_completed_tensor
    (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)) (z₀ z : B.Domain) (a : ℕ)
    (v : Fin a → HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    let γ := SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j L.coordinates hL
    let Z := L.period z.val
    RepresentationTheory.Theta.Adelic.DataTheta.completedTensor (SingleLineComponents.CM.directSingleLineComparison K Q hμ j)
      (directSingleNativeFiniteInput K Q hμ j L.coordinates hL φ) a
      ((SingleLineComponents.CM.directSingleLineComparison K Q hμ j).period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).matrix
      (fun i j => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks γ).jacobiChange Z (v i) ((SingleLineFrame.CM.sourceSingleIndexEquiv K places).symm j)) =
      ((Nat.factorial a : ℂ)⁻¹) *
        (SingleLineHalfRatio.CM.singleSourceNativeHalfRatio K d Q hμ j L hL z₀ *
          ((SingleLineComponents.CM.directSingleLineComparison K Q hμ j).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
            (L.halfDet z.val : ℂ))) *
        iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ Z) 0 v := by
  dsimp only
  have ht := single_source_native_completed_theta_jets K d Q hμ j L hL φ z a v
  have hm := single_source_native_multiplier_factor K d Q hμ j L hL z₀ z
  have he := ht.trans (congrArg (fun c => c * iteratedFDeriv ℂ a
    (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ (L.period z.val)) 0 v) hm)
  have h := congrArg (fun c : ℂ => ((Nat.factorial a : ℂ)⁻¹) * c) he
  simpa only [RepresentationTheory.Theta.Adelic.DataTheta.completedTensor, _root_.smul_apply, smul_eq_mul, mul_assoc] using! h

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineComparison.CM
