import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineGroupAction
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationFrameAction

/-! # Single Line Frame Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineFrameAction.CM

noncomputable section

/-! The fixed source/native frame comparison intertwines the actual
one-line principal action and its dual action. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.GeometricFrame
open OAI.RepresentationTheory.Theta.Adelic.GeometricFrameCocycle.HodgeCovariance OAI.RepresentationTheory.Theta.Adelic.GeometricGroup

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun k v => d k (places.representative v)))
  (hμ : ∀ k, d k (places.representative places.distinguished) = true) (j : Fin 2)
  (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g)

theorem direct_single_frame_coefficients_action (z : B.Domain) (u : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    SingleLineFrame.CM.directSingleLineFrameCoefficients K Q j
      ((SourceFrameAction.CM.sourceFrameMatrix K g hg.2.1 B places (d j) z.val).mulVec u) =
      (RepresentationTheory.Theta.Adelic.BallGeometryData.frameMatrix (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) (SingleLineGroupAction.CM.singleSourceArchimedeanElement K Q N g hg)
        (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).mulVec (SingleLineFrame.CM.directSingleLineFrameCoefficients K Q j u) := by
  let z' := BallLineAction.CM.ballPrincipalAction K B g hg.1 z
  let S := SourceFrameAction.CM.sourceFrameMatrix K g hg.2.1 B places (d j) z.val
  let w := Prescribed.CM.nativePeriodFrame K B places (d j) z.val u
  have hc := (congrArg (SingleLineComponents.CM.directSingleLineComplexComponents K Q hμ j)
    (SourceFrameAction.CM.source_native_frame_transform K g hg.2.1 B places (d j) hg.1 z u)).trans
      (SingleLineFrame.CM.direct_single_line_geometric_frame K d Q hμ j z' (S.mulVec u))
  have ha := SingleLineGroupAction.CM.direct_single_complex_components_action K Q hμ j N g hg w
  have hf := congrArg (RepresentationTheory.Theta.Adelic.BallGeometryData.geometricAction (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j)
    (SingleLineGroupAction.CM.singleSourceArchimedeanElement K Q N g hg)) (SingleLineFrame.CM.direct_single_line_geometric_frame K d Q hμ j z u)
  have hn := RepresentationTheory.Theta.Adelic.GeometricFrameCocycle.HodgeCovariance.geometric_frame_covariance (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j)
    (SingleLineGroupAction.CM.singleSourceArchimedeanElement K Q N g hg) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)
    (SingleLineFrame.CM.directSingleLineFrameCoefficients K Q j u)
  have hb := congrArg (fun y => RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) y
    ((RepresentationTheory.Theta.Adelic.BallGeometryData.frameMatrix (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) (SingleLineGroupAction.CM.singleSourceArchimedeanElement K Q N g hg)
      (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).mulVec (SingleLineFrame.CM.directSingleLineFrameCoefficients K Q j u)))
    (SingleLineGroupAction.CM.direct_single_principal_native_ball_action K Q hμ j N g hg z)
  exact RepresentationTheory.Theta.Adelic.GeometricFrame.geometricFrame_injective (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z')
    (hc.symm.trans (ha.trans (hf.trans (hn.trans hb))))

def directSingleIndexedFrameAction (z : B.Domain) : Matrix (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) ℂ :=
  (RepresentationTheory.Theta.Adelic.BallGeometryData.frameMatrix (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) (SingleLineGroupAction.CM.singleSourceArchimedeanElement K Q N g hg)
    (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)).submatrix (SingleLineFrame.CM.sourceSingleIndexEquiv K places) (SingleLineFrame.CM.sourceSingleIndexEquiv K places)

theorem direct_single_frame_action_matrix (z : B.Domain) :
    SingleLineFrameDeterminant.CM.directSingleIndexedFrameCoefficientMatrix K Q j * SourceFrameAction.CM.sourceFrameMatrix K g hg.2.1 B places (d j) z.val =
      directSingleIndexedFrameAction K d Q hμ j N g hg z * SingleLineFrameDeterminant.CM.directSingleIndexedFrameCoefficientMatrix K Q j := by
  apply Matrix.ext_iff_mulVec.mpr
  intro u
  simp only [← Matrix.mulVec_mulVec]
  have h := congrArg (fun x : Fin places.count × (Fin 3 × Fin 1) → ℂ =>
    fun i => x (SingleLineFrame.CM.sourceSingleIndexEquiv K places i)) (direct_single_frame_coefficients_action K d Q hμ j N g hg z u)
  have hl := SingleLineFrameDeterminant.CM.direct_single_indexed_frame_coefficient_apply K Q j
    ((SourceFrameAction.CM.sourceFrameMatrix K g hg.2.1 B places (d j) z.val).mulVec u)
  have hr := (congrArg (Matrix.mulVec (directSingleIndexedFrameAction K d Q hμ j N g hg z))
    (SingleLineFrameDeterminant.CM.direct_single_indexed_frame_coefficient_apply K Q j u)).trans
      (SourceIntrinsicFrameDeterminant.CM.same_index_matrix_mulVec (SingleLineFrame.CM.sourceSingleIndexEquiv K places)
        (RepresentationTheory.Theta.Adelic.BallGeometryData.frameMatrix (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) (SingleLineGroupAction.CM.singleSourceArchimedeanElement K Q N g hg)
          (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)) (SingleLineFrame.CM.directSingleLineFrameCoefficients K Q j u))
  exact hl.trans (h.trans hr.symm)

theorem direct_single_dual_frame_action (z : B.Domain) (u : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    SingleLineGeometricTensor.CM.directSingleNativeDualCoordinates K d Q j
      ((SourceFrameAction.CM.sourceFrameMatrix K g hg.2.1 B places (d j) z.val)⁻¹ᵀ.mulVec u) =
      RepresentationTheory.Theta.Adelic.BallGeometryData.dualFrameChange (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) (SingleLineGroupAction.CM.singleSourceArchimedeanElement K Q N g hg)
        (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z) (SingleLineGeometricTensor.CM.directSingleNativeDualCoordinates K d Q j u) := by
  have h := congrArg (fun M : Matrix (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) ℂ => M⁻¹ᵀ)
    (direct_single_frame_action_matrix K d Q hμ j N g hg z)
  simp only [Matrix.mul_inv_rev, Matrix.transpose_mul] at h
  have hv := congrArg (fun M => M.mulVec u) h
  simp only [← Matrix.mulVec_mulVec] at hv
  have hi := congrArg (fun x : HeckeCycles.GeometricSource.CM.Positions K places → ℂ =>
    fun k => x ((SingleLineFrame.CM.sourceSingleIndexEquiv K places).symm k)) hv
  have hr := FrameDualTransport.CM.reindexed_inverse_transpose_mulVec (SingleLineFrame.CM.sourceSingleIndexEquiv K places)
    (RepresentationTheory.Theta.Adelic.BallGeometryData.frameMatrix (SingleLineArithmetic.CM.directSingleLineArithmetic K Q hμ j) (SingleLineGroupAction.CM.singleSourceArchimedeanElement K Q N g hg)
      (SourceIntrinsicBall.CM.sourceNativeBallPoint K B z)) ((SingleLineFrameDeterminant.CM.directSingleIndexedFrameCoefficientMatrix K Q j)⁻¹ᵀ.mulVec u)
  exact hi.trans hr

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineFrameAction.CM
