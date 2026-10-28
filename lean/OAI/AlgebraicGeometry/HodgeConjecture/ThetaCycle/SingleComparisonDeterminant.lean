import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleComparisonPeriod
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineFrameDeterminant
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicFrameDeterminant
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceHalfDetAction

/-! # Single Comparison Determinant -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleComparisonDeterminant.CM

noncomputable section

/-! Exact denominator and determinant for any valid native comparison
of the actual source line. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians

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
theorem single_comparison_frame_denominator_apply (z : B.Domain) (x : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN L.coordinates hL)).complexify.denominator
      (L.period z.val).matrix).mulVec x =
      (ComparisonIndexedGraphs.CM.comparisonIndexedFrame N (SingleLineFrame.CM.sourceSingleIndexEquiv K places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).mulVec
        ((SingleLineFrameDeterminant.CM.directSingleIndexedFrameCoefficientMatrix K Q j).mulVec
          (HeckeCycles.GeometricSource.CM.adaptedCoordinates K places (d j) (HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z.val) x))) := by
  let w := HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z.val) x
  let u := HeckeCycles.GeometricSource.CM.adaptedCoordinates K places (d j) w
  have hr : Prescribed.CM.nativePeriodFrame K B places (d j) z.val u = w :=
    AdaptedTotal.CM.native_frame_recovers_line_graph K L z.val z.property x
  have hf := (congrArg (SingleLineComponents.CM.directSingleLineComplexComponents K Q hμ j) hr).symm.trans
    (SingleLineFrame.CM.direct_single_line_geometric_frame K d Q hμ j z u)
  have ht := (SingleComparisonPeriod.CM.single_comparison_complex_transition K Q hμ j N hN L.coordinates w).trans hf
  have hp := ComparisonIndexedGraphs.CM.comparison_indexed_graph_bottom N hG
    (SingleLineFrame.CM.sourceSingleIndexEquiv K places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
    ((SingleComparisonCoordinates.CM.singleComparisonTransitionMatrix K Q hμ j N L.coordinates).map (algebraMap ℚ ℂ) *ᵥ
      SourceSymplecticAction.CM.sourceComplexSumCoordinates K L.coordinates w) (SingleLineFrame.CM.directSingleLineFrameCoefficients K Q j u) ht
  let γ := SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN L.coordinates hL
  have hc := congrArg (fun y => γ.val.map (algebraMap ℚ ℂ) *ᵥ y)
    (SourcePeriodAction.CM.source_graph_sum_coordinates K L.coordinates (L.period z.val) x)
  have hα := hc.trans (MovingTotalPeriod.CM.rational_symplectic_graph_substitution γ (L.period z.val) x)
  have hb := congrArg (fun y : (HeckeCycles.GeometricSource.CM.Positions K places ⊕ HeckeCycles.GeometricSource.CM.Positions K places) → ℂ => fun i => y (.inr i)) hα
  have hbottom := hb.symm.trans hp
  have hidx := SourceIntrinsicFrameDeterminant.CM.same_index_matrix_mulVec (SingleLineFrame.CM.sourceSingleIndexEquiv K places)
    (N.frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).val
    (SingleLineFrame.CM.directSingleLineFrameCoefficients K Q j u)
  have houter := congrArg (Matrix.mulVec (ComparisonIndexedGraphs.CM.comparisonIndexedFrame N (SingleLineFrame.CM.sourceSingleIndexEquiv K places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)))
    (SingleLineFrameDeterminant.CM.direct_single_indexed_frame_coefficient_apply K Q j u)
  exact hbottom.trans (houter.trans hidx).symm

include hG in
theorem single_comparison_frame_denominator_matrix (z : B.Domain) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN L.coordinates hL)).complexify.denominator
      (L.period z.val).matrix =
      ComparisonIndexedGraphs.CM.comparisonIndexedFrame N (SingleLineFrame.CM.sourceSingleIndexEquiv K places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) * SingleLineFrameDeterminant.CM.directSingleIndexedFrameCoefficientMatrix K Q j *
        SourceHalfDetAction.CM.sourceAdaptedGraphMatrix K L z.val := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  simp only [← Matrix.mulVec_mulVec, SourceHalfDetAction.CM.source_adapted_graph_matrix_apply]
  exact single_comparison_frame_denominator_apply K d Q hμ j N hN hG L hL z x

include hG in
theorem single_comparison_frame_denominator_det (z : B.Domain) :
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN L.coordinates hL)).complexify.denominator
      (L.period z.val).matrix).det =
      (N.halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
        (L.halfDet z.val : ℂ)) ^ 2 * (SingleLineFrameDeterminant.CM.directSingleIndexedFrameCoefficientMatrix K Q j).det := by
  have h := congrArg Matrix.det (single_comparison_frame_denominator_matrix K d Q hμ j N hN hG L hL z)
  simp only [Matrix.det_mul] at h
  refine h.trans ?_
  have hf := ComparisonIndexedGraphs.CM.comparison_indexed_frame_det N hG (SingleLineFrame.CM.sourceSingleIndexEquiv K places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
  have hg := SourceHalfDetAction.CM.source_adapted_graph_matrix_det K L z
  have he := congrArg₂ (fun a b : ℂ => a * (SingleLineFrameDeterminant.CM.directSingleIndexedFrameCoefficientMatrix K Q j).det * b) hf hg
  refine he.trans ?_
  ring

include hG in
theorem single_comparison_theta_multiplier_square (z : B.Domain) :
    IndexedCovariance.CM.indexedThetaMultiplier (SingleComparisonCoordinates.CM.singleComparisonSymplecticTransition K Q hμ j N hN L.coordinates hL) (L.period z.val) ^ 2 =
      (N.halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
        (L.halfDet z.val : ℂ)) ^ 2 * (SingleLineFrameDeterminant.CM.directSingleIndexedFrameCoefficientMatrix K Q j).det :=
  (IndexedCovariance.CM.indexed_theta_multiplier_square _ _).trans
    (single_comparison_frame_denominator_det K d Q hμ j N hN hG L hL z)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleComparisonDeterminant.CM
