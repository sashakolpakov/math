import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleAdaptedDualSlots
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationFrameAction
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallProjectiveCotangent

/-! # Single Source Cotangent Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleSourceCotangentAction.CM

noncomputable section

/-! The actual cotangent derivative is the dual action on the fixed
distinguished adapted slots, with exactly one projective denominator
per cotangent argument. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]

def singleAdaptedTangentSlot (places : HeckeCycles.GeometricSource.CM.Places K) (ξ : HeckeCycles.GeometricSource.CM.BallChart) : HeckeCycles.GeometricSource.CM.Positions K places → ℂ :=
  ∑ i : Fin 2, ξ i • SingleAdaptedDualSlots.CM.singleAdaptedDualSlot K places i

omit [IsGalois ℚ K] in
theorem single_adapted_tangent_pairing (places : HeckeCycles.GeometricSource.CM.Places K) (c : HeckeCycles.GeometricSource.CM.Positions K places → ℂ)
    (ξ : HeckeCycles.GeometricSource.CM.BallChart) :
    dotProduct c (singleAdaptedTangentSlot K places ξ) =
      CMExtraction.FrameProjection.Multiplicity.coordinateCovector (fun i => c ((places.distinguished, i.succ))) ξ := by
  simp only [singleAdaptedTangentSlot, Fin.sum_univ_two, dotProduct_add, dotProduct_smul,
    SingleAdaptedDualSlots.CM.singleAdaptedDualSlot, dotProduct_single, smul_eq_mul, mul_one, CMExtraction.FrameProjection.Multiplicity.coordinateCovector_apply]
  ring

variable (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hdet : LinearMap.det g.toLinearMap = 1)
  (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K) (d : Gal(K/ℚ) → Bool)

theorem single_source_frame_distinguished_coordinates (z : HeckeCycles.GeometricSource.CM.BallChart)
    (c : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    (fun i : Fin 2 => (SourceFrameAction.CM.sourceFrameMatrix K g hdet B places d z).mulVec c (places.distinguished, i.succ)) =
      (CMExtraction.UnitaryFrameAction.weightedDualCoordinates (B.b : ℂ) (BallFrameMatrices.CM.ballEmbeddingSL K g hdet (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)) z).mulVec
        (fun i => c (places.distinguished, i.succ)) := by
  funext i
  fin_cases i <;> rw [SourceFrameAction.CM.source_frame_matrix_mulVec]
  all_goals simp [SourceFrameAction.CM.sourceFramePlaceMatrix, BallFrameMatrices.CM.sourceActiveFrameMatrix, CMExtraction.UnitaryFrameAction.activeFrameMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

variable (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y)

include hg

theorem single_source_frame_det_ne_zero (z : B.Domain) :
    (SourceFrameAction.CM.sourceFrameMatrix K g hdet B places d z.val).det ≠ 0 := by
  rw [SourceFrameAction.CM.source_frame_matrix_det K g hdet B places d hg]
  exact pow_ne_zero 2 (BallLineAction.CM.ball_action_denominator_ne_zero K B g hg z)

theorem single_source_tangent_cotangent (z : B.Domain) (c : HeckeCycles.GeometricSource.CM.Positions K places → ℂ)
    (ξ : HeckeCycles.GeometricSource.CM.BallChart) :
    ((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2) *
      dotProduct ((SourceFrameAction.CM.sourceFrameMatrix K g hdet B places d z.val).mulVec c)
        (singleAdaptedTangentSlot K places (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val ξ)) =
      dotProduct c (singleAdaptedTangentSlot K places ξ) := by
  rw [single_adapted_tangent_pairing, single_adapted_tangent_pairing,
    single_source_frame_distinguished_coordinates]
  exact BallProjectiveCotangent.CM.source_ball_projective_cotangent K B g hdet hg z
    (fun i => c ((places.distinguished, i.succ))) ξ

theorem single_source_transpose_tangent (z : B.Domain) (ξ : HeckeCycles.GeometricSource.CM.BallChart) :
    (SourceFrameAction.CM.sourceFrameMatrix K g hdet B places d z.val)ᵀ.mulVec
      (((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2) •
        singleAdaptedTangentSlot K places (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val ξ)) =
      singleAdaptedTangentSlot K places ξ := by
  funext p
  have h := single_source_tangent_cotangent K g hdet B places d hg z (Pi.single p 1) ξ
  simpa only [Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.mulVec_smul,
    Pi.smul_apply, smul_eq_mul] using! h

theorem single_source_dual_tangent (z : B.Domain) (ξ : HeckeCycles.GeometricSource.CM.BallChart) :
    (SourceFrameAction.CM.sourceFrameMatrix K g hdet B places d z.val)⁻¹ᵀ.mulVec
      (singleAdaptedTangentSlot K places ξ) =
      ((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2) •
        singleAdaptedTangentSlot K places (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val ξ) := by
  let S := SourceFrameAction.CM.sourceFrameMatrix K g hdet B places d z.val
  have h := congrArg (Matrix.mulVec S⁻¹ᵀ) (single_source_transpose_tangent K g hdet B places d hg z ξ)
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    Matrix.mul_nonsing_inv S (isUnit_iff_ne_zero.mpr (single_source_frame_det_ne_zero K g hdet B places d hg z)),
    Matrix.transpose_one, Matrix.one_mulVec] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleSourceCotangentAction.CM
