import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteApproximationFrameAction
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallProjectiveCotangent

/-! # Total Source Cotangent Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalSourceCotangentAction.CM

noncomputable section

/-! The actual cotangent derivative is the dual action on the fixed
distinguished adapted slots, with exactly one projective denominator
per cotangent argument. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]

def totalAdaptedTangentSlot (places : HeckeCycles.GeometricSource.CM.Places K) (j : Fin 2) (ξ : HeckeCycles.GeometricSource.CM.BallChart) : PeriodTotal.CM.TotalPositions K places → ℂ :=
  ∑ i : Fin 2, ξ i • TotalAdaptedDualSlots.CM.totalAdaptedDualSlot K places (i, j)

omit [IsGalois ℚ K] in
theorem total_adapted_tangent_pairing (places : HeckeCycles.GeometricSource.CM.Places K) (c : PeriodTotal.CM.TotalPositions K places → ℂ)
    (j : Fin 2) (ξ : HeckeCycles.GeometricSource.CM.BallChart) :
    dotProduct c (totalAdaptedTangentSlot K places j ξ) =
      CMExtraction.FrameProjection.Multiplicity.coordinateCovector (fun i => c (SourceFrameComponents.CM.sourceTotalSlot K places places.distinguished i.succ j)) ξ := by
  simp only [totalAdaptedTangentSlot, Fin.sum_univ_two, dotProduct_add, dotProduct_smul,
    TotalAdaptedDualSlots.CM.totalAdaptedDualSlot, dotProduct_single, smul_eq_mul, mul_one, CMExtraction.FrameProjection.Multiplicity.coordinateCovector_apply]
  ring

variable (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hdet : LinearMap.det g.toLinearMap = 1)
  (B : HeckeCycles.GeometricSource.CM.BallDatum K) (places : HeckeCycles.GeometricSource.CM.Places K) (d : Fin 2 → Gal(K/ℚ) → Bool)

theorem total_source_frame_distinguished_coordinates (z : HeckeCycles.GeometricSource.CM.BallChart)
    (c : PeriodTotal.CM.TotalPositions K places → ℂ) (j : Fin 2) :
    (fun i : Fin 2 => (ConcreteApproximationFrameAction.CM.totalSourceFrameMatrix K g hdet B places d z).mulVec c
      (SourceFrameComponents.CM.sourceTotalSlot K places places.distinguished i.succ j)) =
      (CMExtraction.UnitaryFrameAction.weightedDualCoordinates (B.b : ℂ) (BallFrameMatrices.CM.ballEmbeddingSL K g hdet (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)) z).mulVec
        (fun i => c (SourceFrameComponents.CM.sourceTotalSlot K places places.distinguished i.succ j)) := by
  rw [ConcreteApproximationFrameAction.CM.total_source_frame_matrix_mulVec]
  funext i
  fin_cases j <;> fin_cases i <;> simp [SourceFrameComponents.CM.sourceTotalSlot]
  all_goals rw [SourceFrameAction.CM.source_frame_matrix_mulVec]
  all_goals simp [SourceFrameAction.CM.sourceFramePlaceMatrix, BallFrameMatrices.CM.sourceActiveFrameMatrix, CMExtraction.UnitaryFrameAction.activeFrameMatrix,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

variable (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y)

include hg

theorem total_source_frame_det_ne_zero (z : B.Domain) :
    (ConcreteApproximationFrameAction.CM.totalSourceFrameMatrix K g hdet B places d z.val).det ≠ 0 := by
  rw [ConcreteApproximationFrameAction.CM.totalSourceFrameMatrix, Matrix.det_fromBlocks_zero₂₁,
    SourceFrameAction.CM.source_frame_matrix_det K g hdet B places (d 0) hg,
    SourceFrameAction.CM.source_frame_matrix_det K g hdet B places (d 1) hg]
  exact mul_ne_zero (pow_ne_zero 2 (BallLineAction.CM.ball_action_denominator_ne_zero K B g hg z))
    (pow_ne_zero 2 (BallLineAction.CM.ball_action_denominator_ne_zero K B g hg z))

theorem total_source_tangent_cotangent (z : B.Domain) (c : PeriodTotal.CM.TotalPositions K places → ℂ)
    (j : Fin 2) (ξ : HeckeCycles.GeometricSource.CM.BallChart) :
    ((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2) *
      dotProduct ((ConcreteApproximationFrameAction.CM.totalSourceFrameMatrix K g hdet B places d z.val).mulVec c)
        (totalAdaptedTangentSlot K places j (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val ξ)) =
      dotProduct c (totalAdaptedTangentSlot K places j ξ) := by
  rw [total_adapted_tangent_pairing, total_adapted_tangent_pairing,
    total_source_frame_distinguished_coordinates]
  exact BallProjectiveCotangent.CM.source_ball_projective_cotangent K B g hdet hg z
    (fun i => c (SourceFrameComponents.CM.sourceTotalSlot K places places.distinguished i.succ j)) ξ

theorem total_source_transpose_tangent (z : B.Domain) (j : Fin 2) (ξ : HeckeCycles.GeometricSource.CM.BallChart) :
    (ConcreteApproximationFrameAction.CM.totalSourceFrameMatrix K g hdet B places d z.val)ᵀ.mulVec
      (((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2) •
        totalAdaptedTangentSlot K places j (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val ξ)) =
      totalAdaptedTangentSlot K places j ξ := by
  funext p
  have h := total_source_tangent_cotangent K g hdet B places d hg z (Pi.single p 1) j ξ
  simpa only [Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.mulVec_smul,
    Pi.smul_apply, smul_eq_mul] using! h

theorem total_source_dual_tangent (z : B.Domain) (j : Fin 2) (ξ : HeckeCycles.GeometricSource.CM.BallChart) :
    (ConcreteApproximationFrameAction.CM.totalSourceFrameMatrix K g hdet B places d z.val)⁻¹ᵀ.mulVec
      (totalAdaptedTangentSlot K places j ξ) =
      ((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2) •
        totalAdaptedTangentSlot K places j (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val ξ) := by
  let S := ConcreteApproximationFrameAction.CM.totalSourceFrameMatrix K g hdet B places d z.val
  have h := congrArg (Matrix.mulVec S⁻¹ᵀ) (total_source_transpose_tangent K g hdet B places d hg z j ξ)
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul,
    Matrix.mul_nonsing_inv S (isUnit_iff_ne_zero.mpr (total_source_frame_det_ne_zero K g hdet B places d hg z)),
    Matrix.transpose_one, Matrix.one_mulVec] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.TotalSourceCotangentAction.CM
