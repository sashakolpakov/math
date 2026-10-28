import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLinePeriodGraph
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicFrameDeterminant
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceHalfDetAction

/-! # Single Line Frame Determinant -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineFrameDeterminant.CM

noncomputable section

/-! Exact denominator and determinant of the fixed symplectic transition
for an actual source line. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians

section

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true) (j : Fin 2)

def directSingleIndexedFrame (z : B.Domain) : Matrix (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) ℂ :=
  IntrinsicIndexedGraphs.CM.nativeIndexedFrame (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) (SingleLineComponents.CM.directSingleLineFrames K Q j)
    (SingleLineFrame.CM.sourceSingleIndexEquiv K places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)

def directSingleIndexedFrameCoefficientEquiv :
    (HeckeCycles.GeometricSource.CM.Positions K places → ℂ) ≃ₗ[ℂ] (HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :=
  (SingleLineFrame.CM.directSingleLineFrameCoefficientEquiv K Q j).trans
    (LinearEquiv.funCongrLeft ℂ ℂ (SingleLineFrame.CM.sourceSingleIndexEquiv K places))

def directSingleIndexedFrameCoefficientMatrix : Matrix (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) ℂ :=
  LinearMap.toMatrix' (directSingleIndexedFrameCoefficientEquiv K Q j).toLinearMap

theorem direct_single_indexed_frame_coefficient_apply (u : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    (directSingleIndexedFrameCoefficientMatrix K Q j).mulVec u =
      fun i => SingleLineFrame.CM.directSingleLineFrameCoefficients K Q j u (SingleLineFrame.CM.sourceSingleIndexEquiv K places i) := by
  rw [directSingleIndexedFrameCoefficientMatrix, LinearMap.toMatrix'_mulVec]
  rfl

theorem direct_single_indexed_frame_coefficient_det_ne_zero :
    (directSingleIndexedFrameCoefficientMatrix K Q j).det ≠ 0 := by
  rw [directSingleIndexedFrameCoefficientMatrix, LinearMap.det_toMatrix']
  exact (directSingleIndexedFrameCoefficientEquiv K Q j).isUnit_det'.ne_zero

theorem direct_single_indexed_frame_det (z : B.Domain) :
    (directSingleIndexedFrame K Q hμ j z).det =
      (SingleLineComponents.CM.directSingleLineComparison K Q hμ j).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) ^ 2 :=
  IntrinsicIndexedGraphs.CM.native_indexed_frame_det (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) (SingleLineComponents.CM.directSingleLineFrames K Q j)
    (SingleLineFrame.CM.sourceSingleIndexEquiv K places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)

end

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun k v => d k (places.representative v)))
  (hμ : ∀ k, d k (places.representative places.distinguished) = true) (j : Fin 2)
  (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j)) (hL : L.coordinates.a = Q.a j ∧ L.coordinates.delta = Q.delta)

theorem single_source_native_frame_denominator_apply (z : B.Domain) (x : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j L.coordinates hL)).complexify.denominator
      (L.period z.val).matrix).mulVec x =
      (directSingleIndexedFrame K Q hμ j z).mulVec
        ((directSingleIndexedFrameCoefficientMatrix K Q j).mulVec
          (HeckeCycles.GeometricSource.CM.adaptedCoordinates K places (d j) (HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z.val) x))) := by
  let w := HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z.val) x
  let u := HeckeCycles.GeometricSource.CM.adaptedCoordinates K places (d j) w
  have hr : Prescribed.CM.nativePeriodFrame K B places (d j) z.val u = w :=
    AdaptedTotal.CM.native_frame_recovers_line_graph K L z.val z.property x
  have hf := (congrArg (SingleLineComponents.CM.directSingleLineComplexComponents K Q hμ j) hr).symm.trans
    (SingleLineFrame.CM.direct_single_line_geometric_frame K d Q hμ j z u)
  have ht := (SingleLinePeriodGraph.CM.single_source_native_complex_transition K Q hμ j L.coordinates w).trans hf
  have hp := IntrinsicIndexedGraphs.CM.native_indexed_graph_bottom (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) (SingleLineComponents.CM.directSingleLineFrames K Q j)
    (SingleLineFrame.CM.sourceSingleIndexEquiv K places) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
    ((SingleLineTransition.CM.singleSourceNativeTransitionMatrix K Q hμ j L.coordinates).map (algebraMap ℚ ℂ) *ᵥ
      SourceSymplecticAction.CM.sourceComplexSumCoordinates K L.coordinates w) (SingleLineFrame.CM.directSingleLineFrameCoefficients K Q j u) ht
  let γ := SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j L.coordinates hL
  have hc := congrArg (fun y => γ.val.map (algebraMap ℚ ℂ) *ᵥ y)
    (SourcePeriodAction.CM.source_graph_sum_coordinates K L.coordinates (L.period z.val) x)
  have hα := hc.trans (MovingTotalPeriod.CM.rational_symplectic_graph_substitution γ (L.period z.val) x)
  have hb := congrArg (fun y : (HeckeCycles.GeometricSource.CM.Positions K places ⊕ HeckeCycles.GeometricSource.CM.Positions K places) → ℂ => fun i => y (.inr i)) hα
  have hbottom := hb.symm.trans hp
  have hidx := SourceIntrinsicFrameDeterminant.CM.same_index_matrix_mulVec (SingleLineFrame.CM.sourceSingleIndexEquiv K places)
    ((SingleLineComponents.CM.directSingleLineComparison K Q hμ j).frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).val
    (SingleLineFrame.CM.directSingleLineFrameCoefficients K Q j u)
  have houter := congrArg (Matrix.mulVec (directSingleIndexedFrame K Q hμ j z))
    (direct_single_indexed_frame_coefficient_apply K Q j u)
  exact hbottom.trans (houter.trans hidx).symm

theorem single_source_native_frame_denominator_matrix (z : B.Domain) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j L.coordinates hL)).complexify.denominator
      (L.period z.val).matrix =
      directSingleIndexedFrame K Q hμ j z * directSingleIndexedFrameCoefficientMatrix K Q j *
        SourceHalfDetAction.CM.sourceAdaptedGraphMatrix K L z.val := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  simp only [← Matrix.mulVec_mulVec, SourceHalfDetAction.CM.source_adapted_graph_matrix_apply]
  exact single_source_native_frame_denominator_apply K d Q hμ j L hL z x

theorem single_source_native_frame_denominator_det (z : B.Domain) :
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j L.coordinates hL)).complexify.denominator
      (L.period z.val).matrix).det =
      ((SingleLineComponents.CM.directSingleLineComparison K Q hμ j).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
        (L.halfDet z.val : ℂ)) ^ 2 * (directSingleIndexedFrameCoefficientMatrix K Q j).det := by
  have h := congrArg Matrix.det (single_source_native_frame_denominator_matrix K d Q hμ j L hL z)
  simp only [Matrix.det_mul] at h
  refine h.trans ?_
  have hf := direct_single_indexed_frame_det K Q hμ j z
  have hg := SourceHalfDetAction.CM.source_adapted_graph_matrix_det K L z
  have he := congrArg₂ (fun a b : ℂ => a * (directSingleIndexedFrameCoefficientMatrix K Q j).det * b) hf hg
  refine he.trans ?_
  ring

theorem single_source_native_theta_multiplier_square (z : B.Domain) :
    IndexedCovariance.CM.indexedThetaMultiplier (SingleLineTransition.CM.singleSourceNativeSymplecticTransition K Q hμ j L.coordinates hL) (L.period z.val) ^ 2 =
      ((SingleLineComponents.CM.directSingleLineComparison K Q hμ j).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
        (L.halfDet z.val : ℂ)) ^ 2 * (directSingleIndexedFrameCoefficientMatrix K Q j).det :=
  (IndexedCovariance.CM.indexed_theta_multiplier_square _ _).trans
    (single_source_native_frame_denominator_det K d Q hμ j L hL z)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineFrameDeterminant.CM
