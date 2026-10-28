import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicPeriodGraph
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IndexedCovariance

/-! # Source Intrinsic Frame Determinant -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicFrameDeterminant.CM

noncomputable section

/-! The denominator of the fixed source-to-native symplectic transition
is the product of the actual native frame, its constant source frame
change, and the source adapted graph. Its determinant identifies the
three square-root factors without a compatibility hypothesis. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians

section

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

theorem same_index_matrix_mulVec {I J : Type} [Fintype I] [Fintype J]
    (e : I ≃ J) (M : Matrix J J ℂ) (x : J → ℂ) :
    (M.submatrix e e).mulVec (fun i => x (e i)) = fun i => M.mulVec x (e i) := by
  funext i
  exact e.sum_comp (fun j => M (e i) j * x j)

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true)
  (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)

def directSourceIndexedFrame (z : B.Domain) :
    Matrix (PeriodTotal.CM.TotalPositions K places) (PeriodTotal.CM.TotalPositions K places) ℂ :=
  ((SourceComponents.CM.directSourceComparison K Q hμ hother).frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).val.submatrix
    (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places) (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places)

def directSourceIndexedFrameCoefficientEquiv :
    (PeriodTotal.CM.TotalPositions K places → ℂ) ≃ₗ[ℂ] (PeriodTotal.CM.TotalPositions K places → ℂ) :=
  (SourceIntrinsicTransition.CM.directSourceFrameCoefficientEquiv K Q).trans
    (LinearEquiv.funCongrLeft ℂ ℂ (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places))

def directSourceIndexedFrameCoefficientMatrix :
    Matrix (PeriodTotal.CM.TotalPositions K places) (PeriodTotal.CM.TotalPositions K places) ℂ :=
  LinearMap.toMatrix' (directSourceIndexedFrameCoefficientEquiv K Q).toLinearMap

theorem direct_source_indexed_frame_coefficient_apply (u : PeriodTotal.CM.TotalPositions K places → ℂ) :
    (directSourceIndexedFrameCoefficientMatrix K Q).mulVec u =
      fun i => SourceFrameComponents.CM.directSourceFrameCoefficients K Q u (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places i) := by
  rw [directSourceIndexedFrameCoefficientMatrix, LinearMap.toMatrix'_mulVec]
  rfl

theorem direct_source_indexed_frame_coefficient_det_ne_zero :
    (directSourceIndexedFrameCoefficientMatrix K Q).det ≠ 0 := by
  rw [directSourceIndexedFrameCoefficientMatrix, LinearMap.det_toMatrix']
  exact (directSourceIndexedFrameCoefficientEquiv K Q).isUnit_det'.ne_zero

theorem direct_source_indexed_frame_det (z : B.Domain) :
    (directSourceIndexedFrame K Q hμ hother z).det =
      (SourceComponents.CM.directSourceComparison K Q hμ hother).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) ^ 2 := by
  refine (Matrix.det_submatrix_equiv_self (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places)
    ((SourceComponents.CM.directSourceComparison K Q hμ hother).frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).val).trans ?_
  exact ((RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison_geometry (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother)
    (SourceComponents.CM.directSourceFrames K Q)).2.2.2.2.2.1 (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).2.symm

theorem source_native_phase_graph_bottom (z : B.Domain)
    (α : (PeriodTotal.CM.TotalPositions K places ⊕ PeriodTotal.CM.TotalPositions K places) → ℂ)
    (a : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother) → ℂ)
    (h : SourceIntrinsicTransition.CM.directSourcePhaseRealization K Q hμ hother α =
      RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) a) :
    (fun i => α (.inr i)) = fun i =>
      ((SourceComponents.CM.directSourceComparison K Q hμ hother).frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).val.mulVec a
        (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places i) := by
  let N := SourceComponents.CM.directSourceComparison K Q hμ hother
  let t := (N.frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).val.mulVec a
  have hg : N.complexPhase (Sum.elim t ((N.period (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).matrix.mulVec t)) =
      RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) a :=
    (RepresentationTheory.Theta.Adelic.GeometricGaussians.constructedComparison_geometry (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ hother)
      (SourceComponents.CM.directSourceFrames K Q)).2.2.2.2.2.2.1 (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) a
  have hp := N.complexPhase.injective (h.trans hg.symm)
  funext i
  have he := congrFun hp (.inl (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places i))
  change α (.inr ((SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places).symm (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places i))) =
    t (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places i) at he
  simpa only [Equiv.symm_apply_apply] using! he

omit d Q hμ hother in
theorem source_native_frame_denominator_apply
    (d : Fin 2 → Gal(K/ℚ) → Bool)
    (Q : Lagrangians.CM.LagrangianPair K B places (fun j v => d j (places.representative v)))
    (hμ : ∀ j, d j (places.representative places.distinguished) = true)
    (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)
    (L : (j : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
    (hL : ∀ j, (L j).coordinates.a = Q.a j ∧ (L j).coordinates.delta = Q.delta)
    (z : B.Domain) (x : PeriodTotal.CM.TotalPositions K places → ℂ) :
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K Q hμ hother
      (fun j => (L j).coordinates) hL)).complexify.denominator
        (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)).matrix).mulVec x =
      (directSourceIndexedFrame K Q hμ hother z).mulVec
        ((directSourceIndexedFrameCoefficientMatrix K Q).mulVec
          (AdaptedTotal.CM.totalAdaptedCoordinates K places d
            (TotalPeriodGraphs.CM.totalGraphInAmbient K (fun j => (L j).coordinates)
              (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) x))) := by
  let w := TotalPeriodGraphs.CM.totalGraphInAmbient K (fun j => (L j).coordinates)
    (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) x
  let u := AdaptedTotal.CM.totalAdaptedCoordinates K places d w
  have hrec : AdaptedTotal.CM.totalNativePeriodFrame K B places d z.val u = w :=
    AdaptedTotal.CM.total_native_frame_recovers_graph K L z.val z.property x
  have hf := (congrArg (SourceComponents.CM.directSourceComplexComponents K Q hμ hother) hrec).symm.trans
    (SourceGeometricFrame.CM.direct_source_geometric_frame K d Q hμ hother z u)
  have ht := (SourceIntrinsicTransition.CM.source_native_complex_transition K Q hμ hother (fun j => (L j).coordinates) w).trans hf
  have hp := source_native_phase_graph_bottom K Q hμ hother z
    ((SourceIntrinsicTransition.CM.sourceNativeTransitionMatrix K Q hμ hother (fun j => (L j).coordinates)).map (algebraMap ℚ ℂ) *ᵥ
      ComplexTransition.CM.totalComplexCoordinates K (fun j => (L j).coordinates) w) (SourceFrameComponents.CM.directSourceFrameCoefficients K Q u) ht
  let γ := SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K Q hμ hother (fun j => (L j).coordinates) hL
  have hc := congrArg (fun y => γ.val.map (algebraMap ℚ ℂ) *ᵥ y)
    (TotalPeriodGraphs.CM.total_graph_coordinates K (fun j => (L j).coordinates)
      (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) x)
  have hα := hc.trans (MovingTotalPeriod.CM.rational_symplectic_graph_substitution γ
    (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) x)
  have hb := congrArg (fun y : (PeriodTotal.CM.TotalPositions K places ⊕ PeriodTotal.CM.TotalPositions K places) → ℂ =>
    fun i => y (.inr i)) hα
  have hbottom := hb.symm.trans hp
  have hidx := same_index_matrix_mulVec (SourceIntrinsicTransition.CM.sourceTotalIndexEquiv K places)
    ((SourceComponents.CM.directSourceComparison K Q hμ hother).frame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).val
    (SourceFrameComponents.CM.directSourceFrameCoefficients K Q u)
  have houter := congrArg (Matrix.mulVec (directSourceIndexedFrame K Q hμ hother z))
    (direct_source_indexed_frame_coefficient_apply K Q u)
  exact hbottom.trans (houter.trans hidx).symm

omit d Q hμ hother in
def sourceTotalAdaptedGraphMatrix
    {d : Fin 2 → Gal(K/ℚ) → Bool} (L : (j : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
    (z : HeckeCycles.GeometricSource.CM.BallChart) : Matrix (PeriodTotal.CM.TotalPositions K places) (PeriodTotal.CM.TotalPositions K places) ℂ :=
  LinearMap.toMatrix' ((AdaptedTotal.CM.totalAdaptedCoordinates K places d).comp
    (TotalPeriodGraphs.CM.totalGraphInAmbient K (fun j => (L j).coordinates)
      (BlockPeriod.CM.blockPeriod ((L 0).period z) ((L 1).period z))))

omit d Q hμ hother [IsGalois ℚ K] in
theorem source_total_adapted_graph_matrix_apply
    {d : Fin 2 → Gal(K/ℚ) → Bool} (L : (j : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
    (z : HeckeCycles.GeometricSource.CM.BallChart) (x : PeriodTotal.CM.TotalPositions K places → ℂ) :
    (sourceTotalAdaptedGraphMatrix K L z).mulVec x =
      AdaptedTotal.CM.totalAdaptedCoordinates K places d
        (TotalPeriodGraphs.CM.totalGraphInAmbient K (fun j => (L j).coordinates)
          (BlockPeriod.CM.blockPeriod ((L 0).period z) ((L 1).period z)) x) :=
  LinearMap.toMatrix'_mulVec _ _

omit d Q hμ hother [IsGalois ℚ K] in
theorem source_total_adapted_graph_matrix_det
    {d : Fin 2 → Gal(K/ℚ) → Bool} (L : (j : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
    (z : B.Domain) :
    (sourceTotalAdaptedGraphMatrix K L z.val).det =
      (((L 0).halfDet z.val : ℂ) * ((L 1).halfDet z.val : ℂ)) ^ 2 := by
  rw [sourceTotalAdaptedGraphMatrix, LinearMap.det_toMatrix']
  exact AdaptedTotal.CM.total_adapted_graph_det K L z.val z.property

end

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K}
  (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun j v => d j (places.representative v)))
  (hμ : ∀ j, d j (places.representative places.distinguished) = true)
  (hother : ∃ τ : Gal(K/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)
  (L : (j : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
  (hL : ∀ j, (L j).coordinates.a = Q.a j ∧ (L j).coordinates.delta = Q.delta)

theorem source_native_frame_denominator_matrix (z : B.Domain) :
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K Q hμ hother
      (fun j => (L j).coordinates) hL)).complexify.denominator
        (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)).matrix =
      directSourceIndexedFrame K Q hμ hother z * directSourceIndexedFrameCoefficientMatrix K Q *
        sourceTotalAdaptedGraphMatrix K L z.val := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  simp only [← Matrix.mulVec_mulVec, source_total_adapted_graph_matrix_apply]
  exact source_native_frame_denominator_apply K d Q hμ hother L hL z x

theorem source_native_frame_denominator_det (z : B.Domain) :
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K Q hμ hother
      (fun j => (L j).coordinates) hL)).complexify.denominator
        (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)).matrix).det =
      ((SourceComponents.CM.directSourceComparison K Q hμ hother).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
        (((L 0).halfDet z.val : ℂ) * ((L 1).halfDet z.val : ℂ))) ^ 2 *
          (directSourceIndexedFrameCoefficientMatrix K Q).det := by
  have h := congrArg Matrix.det (source_native_frame_denominator_matrix K d Q hμ hother L hL z)
  simp only [Matrix.det_mul] at h
  refine h.trans ?_
  have hf := direct_source_indexed_frame_det K Q hμ hother z
  have hg := source_total_adapted_graph_matrix_det K L z
  have he := congrArg₂ (fun a b : ℂ => a * (directSourceIndexedFrameCoefficientMatrix K Q).det * b) hf hg
  refine he.trans ?_
  ring

theorem source_native_theta_multiplier_square (z : B.Domain) :
    IndexedCovariance.CM.indexedThetaMultiplier (SourceIntrinsicTransition.CM.sourceNativeSymplecticTransition K Q hμ hother
      (fun j => (L j).coordinates) hL)
        (BlockPeriod.CM.blockPeriod ((L 0).period z.val) ((L 1).period z.val)) ^ 2 =
      ((SourceComponents.CM.directSourceComparison K Q hμ hother).halfFrame (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) *
        (((L 0).halfDet z.val : ℂ) * ((L 1).halfDet z.val : ℂ))) ^ 2 *
          (directSourceIndexedFrameCoefficientMatrix K Q).det :=
  (IndexedCovariance.CM.indexed_theta_multiplier_square _ _).trans
    (source_native_frame_denominator_det K d Q hμ hother L hL z)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicFrameDeterminant.CM
