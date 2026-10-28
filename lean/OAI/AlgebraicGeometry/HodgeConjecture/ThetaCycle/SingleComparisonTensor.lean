import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleComparisonJets
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineGeometricTensor
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleAdaptedDualSlots
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationGeometricTensor

/-! # Single Comparison Tensor -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleComparisonTensor.CM

noncomputable section

/-! The full native tensor of the fixed one-line input equals the actual
source tensor on constant dual coordinates, including the literal
cotangent coefficients of the source one-form. -/

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

include hG in
theorem single_comparison_jacobi_adapted (z : B.Domain) (u : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    (fun k => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN L.coordinates hL)).jacobiChange
      (L.period z.val) ((SourceHalfDetAction.CM.sourceAdaptedGraphMatrix K L z.val)ᵀ.mulVec u)
        ((SingleLineFrame.CM.sourceSingleIndexEquiv K places).symm k)) =
      (N.frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).invᵀ.mulVec
        (SingleLineGeometricTensor.CM.directSingleNativeDualCoordinates K d Q j u) := by
  have hGraph : IsUnit (SourceHalfDetAction.CM.sourceAdaptedGraphMatrix K L z.val).det := by
    rw [SourceHalfDetAction.CM.source_adapted_graph_matrix_det]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero 2 (Units.ne_zero _))
  have h := SingleLineGeometricTensor.CM.single_frame_inverse_transpose_cancel _ _ _ _
    (SingleComparisonDeterminant.CM.single_comparison_frame_denominator_matrix K d Q hμ j N hN hG L hL z) hGraph u
  have hi := congrArg (fun x : HeckeCycles.GeometricSource.CM.Positions K places → ℂ =>
    fun k => x ((SingleLineFrame.CM.sourceSingleIndexEquiv K places).symm k)) h
  have hr := FrameDualTransport.CM.reindexed_inverse_transpose_mulVec (SingleLineFrame.CM.sourceSingleIndexEquiv K places)
    (N.frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).val
    ((SingleLineFrameDeterminant.CM.directSingleIndexedFrameCoefficientMatrix K Q j)⁻¹ᵀ.mulVec u)
  have he := hi.trans hr
  have hinv := Matrix.coe_units_inv (N.frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z))
  have hf := congrArg (fun M : Matrix (Fin places.count × (Fin 3 × Fin 1))
      (Fin places.count × (Fin 3 × Fin 1)) ℂ =>
    Mᵀ.mulVec (SingleLineGeometricTensor.CM.directSingleNativeDualCoordinates K d Q j u)) hinv
  simpa only [ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.jacobiChange_apply] using! he.trans hf.symm

include hG in
theorem single_comparison_geometric_tensor (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places))
    (z₀ z : B.Domain) (a : ℕ) (u : Fin a → HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor N
      (SingleComparison.CM.singleComparisonFiniteInput K Q hμ j N hN L.coordinates hL φ) a
      (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) (fun k => SingleLineGeometricTensor.CM.directSingleNativeDualCoordinates K d Q j (u k)) =
      ((Nat.factorial a : ℂ)⁻¹) * SingleComparisonHalfRatio.CM.singleComparisonHalfRatio K d Q hμ j N hN L hL z₀ *
        (L.halfDet z.val : ℂ) * iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ (L.period z.val)) 0
          (fun k => (SourceHalfDetAction.CM.sourceAdaptedGraphMatrix K L z.val)ᵀ.mulVec (u k)) := by
  let q := N.halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
  have hq : q ≠ 0 :=
    (mul_ne_zero_iff.mp (SingleComparisonHalfRatio.CM.single_comparison_half_denominator_ne_zero K d Q hμ j N hG L z)).1
  have hj : (fun k i => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN L.coordinates hL)).jacobiChange
      (L.period z.val) ((SourceHalfDetAction.CM.sourceAdaptedGraphMatrix K L z.val)ᵀ.mulVec (u k))
        ((SingleLineFrame.CM.sourceSingleIndexEquiv K places).symm i)) =
      (fun k => (N.frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).invᵀ.mulVec
        (SingleLineGeometricTensor.CM.directSingleNativeDualCoordinates K d Q j (u k))) :=
    funext (fun k => single_comparison_jacobi_adapted K d Q hμ j N hN hG L hL z (u k))
  have ht := SingleComparisonJets.CM.single_comparison_completed_tensor K d Q hμ j N hN hG L hL φ z₀ z a
    (fun k => (SourceHalfDetAction.CM.sourceAdaptedGraphMatrix K L z.val)ᵀ.mulVec (u k))
  have hx := congrArg (RepresentationTheory.Theta.Adelic.DataTheta.completedTensor N
    (SingleComparison.CM.singleComparisonFiniteInput K Q hμ j N hN L.coordinates hL φ) a
    (N.period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).matrix) hj
  have hs := congrArg (fun c : ℂ => q⁻¹ * c) (hx.symm.trans ht)
  exact hs.trans (ConcreteApproximationGeometricTensor.CM.inverse_half_frame_cancel _ _ _ _ _ hq)

include hG in
theorem single_comparison_geometric_source_slot (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places))
    (z₀ z : B.Domain) (i : Fin 2) :
    RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor N
      (SingleComparison.CM.singleComparisonFiniteInput K Q hμ j N hN L.coordinates hL φ) 1
      (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
      (fun _ => SingleLineGeometricTensor.CM.directSingleNativeDualCoordinates K d Q j (SingleAdaptedDualSlots.CM.singleAdaptedDualSlot K places i)) =
      SingleComparisonHalfRatio.CM.singleComparisonHalfRatio K d Q hμ j N hN L hL z₀ * Slots.CM.sourceThetaCoordinates K L φ z.val i := by
  have h := single_comparison_geometric_tensor K d Q hμ j N hN hG L hL φ z₀ z 1
    (fun _ => SingleAdaptedDualSlots.CM.singleAdaptedDualSlot K places i)
  simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_mul, iteratedFDeriv_one_apply,
    ← SingleAdaptedDualSlots.CM.theta_jacobi_slot_adapted_transpose] at h
  exact h.trans (by rw [Slots.CM.source_coordinates_completed_slots]; exact mul_assoc _ _ _)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleComparisonTensor.CM
