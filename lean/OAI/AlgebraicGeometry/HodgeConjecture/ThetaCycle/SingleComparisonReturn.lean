import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleComparisonTensor
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ComparisonReturnTensor

/-! # Single Comparison Return -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleComparisonReturn.CM

noncomputable section

/-! Every actual native one-line finite input returns to one fixed source
input. Its full tensor and literal cotangent coefficients agree with the
source form through one explicit nonzero constant on the ball. -/

open scoped Classical _root_.NumberField _root_.Matrix _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun k v => d k (places.representative v)))
  (hμ : ∀ k, d k (places.representative places.distinguished) = true) (j : Fin 2)
  (N : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData _ _ _ (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j))
  (hN : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification N (SingleLineComponents.CM.directSingleLineFrames K Q j))
  (hG : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification N)
  (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j)) (hL : L.coordinates.a = Q.a j ∧ L.coordinates.delta = Q.delta)

def singleComparisonReturnedInput
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (maximalRealSubfield K) (3 * 1)) :
    RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places) :=
  ComparisonReturnTensor.CM.comparisonReturnInput N (SingleLineFrame.CM.sourceSingleIndexEquiv K places)
    (SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN L.coordinates hL) f

def singleComparisonReturnConstant (z₀ : B.Domain) : ℂ :=
  (IndexedInverseMultiplier.CM.indexedInverseMultiplier (SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN L.coordinates hL)
    (L.period z₀.val))⁻¹ * SingleComparisonHalfRatio.CM.singleComparisonHalfRatio K d Q hμ j N hN L hL z₀

include hG in
theorem single_comparison_return_constant_ne_zero (z₀ : B.Domain) :
    singleComparisonReturnConstant K d Q hμ j N hN L hL z₀ ≠ 0 :=
  mul_ne_zero (inv_ne_zero (IndexedInverseMultiplier.CM.indexed_inverse_multiplier_ne_zero _ _))
    (SingleComparisonHalfRatio.CM.single_comparison_half_ratio_ne_zero K d Q hμ j N hN hG L hL z₀)

include hG in
theorem single_comparison_return_tensor
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (maximalRealSubfield K) (3 * 1))
    (z₀ z : B.Domain) (a : ℕ) (u : Fin a → HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor N f a (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
        (fun k => SingleLineGeometricTensor.CM.directSingleNativeDualCoordinates K d Q j (u k)) =
      ((Nat.factorial a : ℂ)⁻¹) * singleComparisonReturnConstant K d Q hμ j N hN L hL z₀ *
        (L.halfDet z.val : ℂ) * iteratedFDeriv ℂ a
          (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed (singleComparisonReturnedInput K d Q hμ j N hN L hL f) (L.period z.val)) 0
          (fun k => (SourceHalfDetAction.CM.sourceAdaptedGraphMatrix K L z.val)ᵀ.mulVec (u k)) := by
  let γ := SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN L.coordinates hL
  let φ := singleComparisonReturnedInput K d Q hμ j N hN L hL f
  let σ := IndexedInverseMultiplier.CM.indexedInverseMultiplier γ (L.period z₀.val)
  have hσ : σ ≠ 0 := IndexedInverseMultiplier.CM.indexed_inverse_multiplier_ne_zero _ _
  have : ConnectedSpace B.domain := BallConnected.CM.ball_domain_connected B
  have : Nonempty (HeckeCycles.GeometricSource.CM.Positions K places) := ⟨(places.distinguished, 0)⟩
  have hc := IndexedInverseMultiplier.CM.indexed_inverse_multiplier_constant γ L.period L.holomorphic z₀ z
  have hr := ComparisonReturnTensor.CM.comparison_return_geometric_tensor N (SingleLineFrame.CM.sourceSingleIndexEquiv K places) γ f
    (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) (L.period z.val)
    (SingleComparisonPeriod.CM.single_comparison_period_transform K d Q hμ j N hN hG L hL z) a
    (fun k => SingleLineGeometricTensor.CM.directSingleNativeDualCoordinates K d Q j (u k))
  have hs := SingleComparisonTensor.CM.single_comparison_geometric_tensor K d Q hμ j N hN hG L hL φ z₀ z a u
  have hp := congrArg (fun c : ℂ => c * RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor N f a (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
    (fun k => SingleLineGeometricTensor.CM.directSingleNativeDualCoordinates K d Q j (u k))) hc
  have he := hp.symm.trans (hr.symm.trans hs)
  have h := congrArg (fun c : ℂ => σ⁻¹ * c) he
  rw [inv_mul_cancel_left₀ hσ] at h
  exact h.trans (by dsimp only [singleComparisonReturnConstant]; ring)

include hG in
theorem single_comparison_return_source_slot
    (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (maximalRealSubfield K) (3 * 1))
    (z₀ z : B.Domain) (i : Fin 2) :
    RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor N f 1 (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
        (fun _ => SingleLineGeometricTensor.CM.directSingleNativeDualCoordinates K d Q j (SingleAdaptedDualSlots.CM.singleAdaptedDualSlot K places i)) =
      singleComparisonReturnConstant K d Q hμ j N hN L hL z₀ *
        Slots.CM.sourceThetaCoordinates K L (singleComparisonReturnedInput K d Q hμ j N hN L hL f) z.val i := by
  have h := single_comparison_return_tensor K d Q hμ j N hN hG L hL f z₀ z 1
    (fun _ => SingleAdaptedDualSlots.CM.singleAdaptedDualSlot K places i)
  simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_mul, iteratedFDeriv_one_apply,
    ← SingleAdaptedDualSlots.CM.theta_jacobi_slot_adapted_transpose] at h
  exact h.trans (by rw [Slots.CM.source_coordinates_completed_slots]; exact mul_assoc _ _ _)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleComparisonReturn.CM
