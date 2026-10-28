import OAI.RepresentationTheory.Theta.Adelic.PeriodPlaceProjection
import OAI.RepresentationTheory.Theta.Adelic.PositionPlaceProjection

/-! # Period Cross Terms -/

namespace OAI.RepresentationTheory.Theta.Adelic.PeriodCrossTerms

noncomputable section

/-! Cross terms between different archimedean position spaces vanish in
the actual geometric period form. This is a consequence of the place
decomposition of its positive Hodge graph and the trace pairing. -/

open scoped Classical _root_.NumberField

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates
open OAI.RepresentationTheory.Theta.Adelic.ComplexIntrinsicAction.Coordinate OAI.RepresentationTheory.Theta.Adelic.PeriodPlaceProjection OAI.RepresentationTheory.Theta.Adelic.LocalPositionInclusion
open OAI.RepresentationTheory.Theta.Adelic.PositionPlaceProjection OAI.RepresentationTheory.Theta.Adelic.PositionPlaceProjection.Pure

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K) (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem complex_projection_other_graph (v w : Fin A.places) (hvw : v ≠ w)
    (z : BallNatural.Ball) (y : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)) :
    ComplexIntrinsicAction.Coordinate.complexifiedLinear (PeriodPlaceProjection.realPlaceProjection A v)
      (Sum.elim (fun i => ((LocalPositionInclusion.realPositionColumn A w).mulVec y i : ℂ))
        ((PeriodCoordinates.geometricPeriod A P z).matrix.mulVec (fun i => ((LocalPositionInclusion.realPositionColumn A w).mulVec y i : ℂ)))) = 0 := by
  obtain ⟨q, hq⟩ := PeriodPlaceProjection.projection_preserves_period_graph A P v z
    (fun i => ((LocalPositionInclusion.realPositionColumn A w).mulVec y i : ℂ))
  have hp := congrArg (PositionPlaceProjection.positionPart (R := ℂ) (I := BallGeometryData.FrameIndex A)) hq
  rw [PositionPlaceProjection.complexPlaceProjection_position] at hp
  change ComplexIntrinsicAction.Coordinate.complexifiedLinear (PositionPlaceProjection.positionPlaceProjection A v)
    (fun i => ((LocalPositionInclusion.realPositionColumn A w).mulVec y i : ℂ)) = q at hp
  rw [PositionPlaceProjection.complexPositionProjection_column_ne A v w hvw] at hp
  rw [← hp, Matrix.mulVec_zero] at hq
  exact hq.trans (by funext i; cases i <;> rfl)

theorem period_cross_terms_zero (v w : Fin A.places) (hvw : v ≠ w)
    (z : BallNatural.Ball) (x y : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ (3 * m)) :
    AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm (PeriodCoordinates.geometricPeriod A P z).matrix
      ((LocalPositionInclusion.realPositionColumn A v).mulVec x) ((LocalPositionInclusion.realPositionColumn A w).mulVec y) = 0 := by
  have h := PeriodPlaceProjection.complex_projection_pairing A P v
    (Sum.elim (fun i => ((LocalPositionInclusion.realPositionColumn A v).mulVec x i : ℂ)) 0)
    (Sum.elim (fun i => ((LocalPositionInclusion.realPositionColumn A w).mulVec y i : ℂ))
      ((PeriodCoordinates.geometricPeriod A P z).matrix.mulVec (fun i => ((LocalPositionInclusion.realPositionColumn A w).mulVec y i : ℂ))))
  rw [PositionPlaceProjection.Pure.complexPlaceProjection_pure_position, complex_projection_other_graph A P v w hvw] at h
  simp only [DataTheta.standardPairing, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
    zero_mul, mul_zero, sub_zero, Finset.sum_const_zero, Matrix.mulVec, dotProduct, Finset.mul_sum] at h
  simpa only [AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.siegelMatrixForm_apply, Matrix.mulVec, dotProduct, mul_comm, mul_left_comm, mul_assoc] using h

end

end OAI.RepresentationTheory.Theta.Adelic.PeriodCrossTerms
