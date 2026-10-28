import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumJets
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineGeometricTensor
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalAdaptedDualSlots
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationGeometricTensor

/-! # Intrinsic Kernel Sum Tensor -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumTensor.CM

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
  (hμ : ∀ k, d k (places.representative places.distinguished) = true)
  (N : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData _ _ _ (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ))
  (hN : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification N (IntrinsicKernelArithmetic.CM.directSourceNativeSumFrames K Q))
  (hG : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification N)
  (L : (j : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
  (hL : ∀ j, (L j).coordinates.a = Q.a j ∧ (L j).coordinates.delta = Q.delta)

def sumComparisonDualCoordinates (u : PeriodTotal.CM.TotalPositions K places → ℂ) :
    Fin places.count × (Fin 3 × Fin 2) → ℂ :=
  fun k => (SourceIntrinsicFrameDeterminant.CM.directSourceIndexedFrameCoefficientMatrix K Q)⁻¹ᵀ.mulVec u
    ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).symm k)

include hG in
theorem sum_comparison_jacobi_adapted (z : B.Domain) (u : PeriodTotal.CM.TotalPositions K places → ℂ) :
    (fun k => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN (fun j => (L j).coordinates) hL)).jacobiChange
      (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) ((SourceIntrinsicFrameDeterminant.CM.sourceTotalAdaptedGraphMatrix K L z.val)ᵀ.mulVec u)
        ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).symm k)) =
      (N.frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).invᵀ.mulVec
        (sumComparisonDualCoordinates K d Q u) := by
  have hGraph : IsUnit (SourceIntrinsicFrameDeterminant.CM.sourceTotalAdaptedGraphMatrix K L z.val).det := by
    rw [SourceIntrinsicFrameDeterminant.CM.source_total_adapted_graph_matrix_det]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero 2 (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)))
  have h := SingleLineGeometricTensor.CM.single_frame_inverse_transpose_cancel _ _ _ _
    (IntrinsicKernelSumDeterminant.CM.sum_comparison_frame_denominator_matrix K d Q hμ N hN hG L hL z) hGraph u
  have hi := congrArg (fun x : PeriodTotal.CM.TotalPositions K places → ℂ =>
    fun k => x ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).symm k)) h
  have hr := FrameDualTransport.CM.reindexed_inverse_transpose_mulVec (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places)
    (N.frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).val
    ((SourceIntrinsicFrameDeterminant.CM.directSourceIndexedFrameCoefficientMatrix K Q)⁻¹ᵀ.mulVec u)
  have he := hi.trans hr
  have hinv := Matrix.coe_units_inv (N.frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z))
  have hf := congrArg (fun M : Matrix (Fin places.count × (Fin 3 × Fin 2))
      (Fin places.count × (Fin 3 × Fin 2)) ℂ =>
    Mᵀ.mulVec (sumComparisonDualCoordinates K d Q u)) hinv
  simpa only [ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks.jacobiChange_apply] using! he.trans hf.symm

include hG in
theorem sum_comparison_geometric_tensor (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K places))
    (z₀ z : B.Domain) (a : ℕ) (u : Fin a → PeriodTotal.CM.TotalPositions K places → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor N
      (IntrinsicKernelSum.CM.sumComparisonFiniteInput K Q hμ N hN (fun j => (L j).coordinates) hL φ) a
      (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) (fun k => sumComparisonDualCoordinates K d Q (u k)) =
      ((Nat.factorial a : ℂ)⁻¹) * KernelSumHalfRatio.CM.sumComparisonHalfRatio K d Q hμ N hN L hL z₀ *
        (((L 0).halfDet z.val : ℂ) * ((L 1).halfDet z.val : ℂ)) * iteratedFDeriv ℂ a (RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.completed φ (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val))) 0
          (fun k => (SourceIntrinsicFrameDeterminant.CM.sourceTotalAdaptedGraphMatrix K L z.val)ᵀ.mulVec (u k)) := by
  let q := N.halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
  have hq : q ≠ 0 :=
    (mul_ne_zero_iff.mp (KernelSumHalfRatio.CM.sum_comparison_half_denominator_ne_zero K d Q hμ N hG L z)).1
  have hj : (fun k i => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN (fun j => (L j).coordinates) hL)).jacobiChange
      (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) ((SourceIntrinsicFrameDeterminant.CM.sourceTotalAdaptedGraphMatrix K L z.val)ᵀ.mulVec (u k))
        ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).symm i)) =
      (fun k => (N.frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).invᵀ.mulVec
        (sumComparisonDualCoordinates K d Q (u k))) :=
    funext (fun k => sum_comparison_jacobi_adapted K d Q hμ N hN hG L hL z (u k))
  have ht := IntrinsicKernelSumJets.CM.sum_comparison_completed_tensor K d Q hμ N hN hG L hL φ z₀ z a
    (fun k => (SourceIntrinsicFrameDeterminant.CM.sourceTotalAdaptedGraphMatrix K L z.val)ᵀ.mulVec (u k))
  have hx := congrArg (RepresentationTheory.Theta.Adelic.DataTheta.completedTensor N
    (IntrinsicKernelSum.CM.sumComparisonFiniteInput K Q hμ N hN (fun j => (L j).coordinates) hL φ) a
    (N.period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).matrix) hj
  have hs := congrArg (fun c : ℂ => q⁻¹ * c) (hx.symm.trans ht)
  exact hs.trans (ConcreteApproximationGeometricTensor.CM.inverse_half_frame_cancel _ _ _ _ _ hq)

include hG in
theorem sum_comparison_geometric_source_slots (φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K places))
    (z₀ z : B.Domain) (a b : Fin 2 × Fin 2) :
    RepresentationTheory.Theta.Adelic.DataTheta.geometricTensor N (IntrinsicKernelSum.CM.sumComparisonFiniteInput K Q hμ N hN (fun j => (L j).coordinates) hL φ) 2
      (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
      ![sumComparisonDualCoordinates K d Q (TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K places a),
        sumComparisonDualCoordinates K d Q (TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K places b)] =
      (2 : ℂ)⁻¹ * KernelSumHalfRatio.CM.sumComparisonHalfRatio K d Q hμ N hN L hL z₀ *
        InitialTensor.CM.splitThetaTensor K (L 0) (L 1) φ z.val a b := by
  have h := sum_comparison_geometric_tensor K d Q hμ N hN hG L hL φ z₀ z 2
    ![TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K places a, TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K places b]
  have hu : (fun j : Fin 2 => sumComparisonDualCoordinates K d Q
      (![TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K places a, TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K places b] j)) =
      ![sumComparisonDualCoordinates K d Q (TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K places a),
        sumComparisonDualCoordinates K d Q (TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K places b)] := by
    funext j
    fin_cases j <;> rfl
  have hv : (fun j : Fin 2 => (SourceIntrinsicFrameDeterminant.CM.sourceTotalAdaptedGraphMatrix K L z.val)ᵀ.mulVec
      (![TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K places a, TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K places b] j)) =
      ![InitialTensor.CM.splitThetaSlot K (L 0) (L 1) z.val a,
        InitialTensor.CM.splitThetaSlot K (L 0) (L 1) z.val b] := by
    funext j
    fin_cases j
    · exact (TotalAdaptedDualSlots.CM.split_theta_slot_adapted_transpose K L z.val a).symm
    · exact (TotalAdaptedDualSlots.CM.split_theta_slot_adapted_transpose K L z.val b).symm
  rw [hu, hv, show (Nat.factorial 2 : ℂ) = 2 from by norm_num] at h
  simpa only [InitialTensor.CM.splitThetaTensor, mul_assoc] using! h

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumTensor.CM
