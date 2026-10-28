import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumPeriod
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicFrameDeterminant
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IndexedCovariance

/-! # Intrinsic Kernel Sum Determinant -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumDeterminant.CM

noncomputable section

/-! The denominator of the fixed source-to-native symplectic transition
is the product of the actual native frame, its constant source frame
change, and the source adapted graph. Its determinant identifies the
three square-root factors without a compatibility hypothesis. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
  (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun j v => d j (places.representative v)))
  (hμ : ∀ j, d j (places.representative places.distinguished) = true)
  (N : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData _ _ _ (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ))
  (hN : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification N (IntrinsicKernelArithmetic.CM.directSourceNativeSumFrames K Q))
  (hG : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification N)
  (L : (j : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
  (hL : ∀ j, (L j).coordinates.a = Q.a j ∧ (L j).coordinates.delta = Q.delta)

include hG in
theorem sum_comparison_frame_denominator_apply
    (z : B.Domain) (x : PeriodTotal.CM.TotalPositions K places → ℂ) :
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN
      (fun j => (L j).coordinates) hL)).complexify.denominator
        (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)).matrix).mulVec x =
      (ComparisonIndexedGraphs.CM.comparisonIndexedFrame N (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).mulVec
        ((SourceIntrinsicFrameDeterminant.CM.directSourceIndexedFrameCoefficientMatrix K Q).mulVec
          (AdaptedTotal.CM.totalAdaptedCoordinates K places d
            (TotalPeriodGraphs.CM.totalGraphInAmbient K (fun j => (L j).coordinates)
              (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) x))) := by
  let w := TotalPeriodGraphs.CM.totalGraphInAmbient K (fun j => (L j).coordinates)
    (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) x
  let u := AdaptedTotal.CM.totalAdaptedCoordinates K places d w
  have hrec : AdaptedTotal.CM.totalNativePeriodFrame K B places d z.val u = w :=
    AdaptedTotal.CM.total_native_frame_recovers_graph K L z.val z.property x
  have hf := (congrArg (SourceComponents.CM.directSourceComplexComponents K Q hμ B.other_place) hrec).symm.trans
    (IntrinsicKernelSumPeriod.CM.native_c38_source_geometric_frame K d Q hμ z u)
  have ht := (KernelSumComplexTransition.CM.sum_comparison_complex_transition K Q hμ N hN (fun j => (L j).coordinates) w).trans hf
  have hp := ComparisonIndexedGraphs.CM.comparison_indexed_graph_bottom N hG (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
    ((IntrinsicKernelSumTransition.CM.sumComparisonTransitionMatrix K Q hμ N (fun j => (L j).coordinates)).map (algebraMap ℚ ℂ) *ᵥ
      ComplexTransition.CM.totalComplexCoordinates K (fun j => (L j).coordinates) w) (SourceFrameComponents.CM.directSourceFrameCoefficients K Q u) ht
  let γ := IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN (fun j => (L j).coordinates) hL
  have hc := congrArg (fun y => γ.val.map (algebraMap ℚ ℂ) *ᵥ y)
    (TotalPeriodGraphs.CM.total_graph_coordinates K (fun j => (L j).coordinates)
      (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) x)
  have hα := hc.trans (MovingTotalPeriod.CM.rational_symplectic_graph_substitution γ
    (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) x)
  have hb := congrArg (fun y : (PeriodTotal.CM.TotalPositions K places ⊕ PeriodTotal.CM.TotalPositions K places) → ℂ =>
    fun i => y (.inr i)) hα
  have hbottom := hb.symm.trans hp
  have hidx := SourceIntrinsicFrameDeterminant.CM.same_index_matrix_mulVec (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places)
    (N.frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).val
    (SourceFrameComponents.CM.directSourceFrameCoefficients K Q u)
  have houter := congrArg (Matrix.mulVec (ComparisonIndexedGraphs.CM.comparisonIndexedFrame N (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)))
    (SourceIntrinsicFrameDeterminant.CM.direct_source_indexed_frame_coefficient_apply K Q u)
  exact hbottom.trans (houter.trans hidx).symm

include hG in
theorem sum_comparison_frame_denominator_matrix (z : B.Domain) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN
      (fun j => (L j).coordinates) hL)).complexify.denominator
        (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)).matrix =
      ComparisonIndexedGraphs.CM.comparisonIndexedFrame N (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) * SourceIntrinsicFrameDeterminant.CM.directSourceIndexedFrameCoefficientMatrix K Q *
        SourceIntrinsicFrameDeterminant.CM.sourceTotalAdaptedGraphMatrix K L z.val := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  simp only [← Matrix.mulVec_mulVec, SourceIntrinsicFrameDeterminant.CM.source_total_adapted_graph_matrix_apply]
  exact sum_comparison_frame_denominator_apply K d Q hμ N hN hG L hL z x

include hG in
theorem sum_comparison_frame_denominator_det (z : B.Domain) :
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN
      (fun j => (L j).coordinates) hL)).complexify.denominator
        (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)).matrix).det =
      (N.halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
        (((L 0).halfDet z.val : ℂ) * ((L 1).halfDet z.val : ℂ))) ^ 2 *
          (SourceIntrinsicFrameDeterminant.CM.directSourceIndexedFrameCoefficientMatrix K Q).det := by
  have h := congrArg Matrix.det (sum_comparison_frame_denominator_matrix K d Q hμ N hN hG L hL z)
  simp only [Matrix.det_mul] at h
  refine h.trans ?_
  have hf := ComparisonIndexedGraphs.CM.comparison_indexed_frame_det N hG (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
  have hg := SourceIntrinsicFrameDeterminant.CM.source_total_adapted_graph_matrix_det K L z
  have he := congrArg₂ (fun a b : ℂ => a * (SourceIntrinsicFrameDeterminant.CM.directSourceIndexedFrameCoefficientMatrix K Q).det * b) hf hg
  refine he.trans ?_
  ring

include hG in
theorem sum_comparison_theta_multiplier_square (z : B.Domain) :
    IndexedCovariance.CM.indexedThetaMultiplier (IntrinsicKernelSumTransition.CM.sumComparisonSymplecticTransition K Q hμ N hN
      (fun j => (L j).coordinates) hL)
        (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) ^ 2 =
      (N.halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
        (((L 0).halfDet z.val : ℂ) * ((L 1).halfDet z.val : ℂ))) ^ 2 *
          (SourceIntrinsicFrameDeterminant.CM.directSourceIndexedFrameCoefficientMatrix K Q).det :=
  (IndexedCovariance.CM.indexed_theta_multiplier_square _ _).trans
    (sum_comparison_frame_denominator_det K d Q hμ N hN hG L hL z)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumDeterminant.CM
