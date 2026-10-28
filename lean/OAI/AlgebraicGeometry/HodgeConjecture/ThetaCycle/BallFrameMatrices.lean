import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallAmbientPairing
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryFrameAction

/-! # Ball Frame Matrices -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallFrameMatrices.CM

noncomputable section

/-! ThetaCycle: actual determinant-one embedding matrices and the weighted
line-annihilator frame action for the original ball coefficient. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.UnitaryFrameAction

variable (K : IntermediateField ℚ ℂ) [IsGalois ℚ K]
  (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hdet : LinearMap.det g.toLinearMap = 1)

def ballEmbeddingSL (τ : Gal(K/ℚ)) : Matrix.SpecialLinearGroup (Fin 3) ℂ := by
  refine ⟨SourceSymplecticAction.CM.ballEmbeddingMatrix K g τ, ?_⟩
  have he := (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K τ).toRingHom.map_det (LinearMap.toMatrix' g.toLinearMap)
  rw [LinearMap.det_toMatrix', hdet, map_one] at he
  exact he.symm

theorem ball_embedding_sl_chart (z : HeckeCycles.GeometricSource.CM.BallChart) :
    RepresentationTheory.Theta.Adelic.DeterminantCoordinates.chartImage (ballEmbeddingSL K g hdet 1) z = HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z := rfl

theorem ball_embedding_sl_denominator (z : HeckeCycles.GeometricSource.CM.BallChart) :
    RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator (ballEmbeddingSL K g hdet 1) z =
      (BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z) 2 := rfl

variable [NumberField K] [NumberField.IsCMField K] (B : HeckeCycles.GeometricSource.CM.BallDatum K)
  (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y)

include hg in
theorem ball_embedding_sl_cross :
    (ballEmbeddingSL K g hdet 1).val.transpose * CMExtraction.UnitaryFrameAction.diagonalForm (B.b : ℂ) *
      (ballEmbeddingSL K g hdet (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)).val = CMExtraction.UnitaryFrameAction.diagonalForm (B.b : ℂ) := by
  have hD : CMExtraction.UnitaryFrameAction.diagonalForm (B.b : ℂ) =
      Matrix.diagonal (fun i : Fin 3 => if i = 2 then (B.b : ℂ) else 1) := by
    apply congrArg Matrix.diagonal
    funext i
    fin_cases i <;> rfl
  rw [hD]
  simpa only [mul_one] using! BallAmbientPairing.CM.ball_embedding_pairing_matrix K B g hg 1

def sourceActiveFrameMatrix (z : HeckeCycles.GeometricSource.CM.BallChart) : Matrix (Fin 3) (Fin 3) ℂ :=
  CMExtraction.UnitaryFrameAction.activeFrameMatrix (B.b : ℂ) (ballEmbeddingSL K g hdet 1)
    (ballEmbeddingSL K g hdet (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)) z

include hg in
theorem source_active_frame_matrix_det (z : HeckeCycles.GeometricSource.CM.BallChart) :
    (sourceActiveFrameMatrix K g hdet B z).det =
      ((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z) 2) ^ 2 :=
  CMExtraction.UnitaryFrameAction.activeFrameMatrix_det (B.b : ℂ) (fun hb => (ne_of_lt B.negative) (by rw [hb]; rfl))
    _ _ (ball_embedding_sl_cross K g hdet B hg) z

include hg in
theorem source_weighted_frame_transform (z : B.Domain) (u : Fin 3 → ℂ) :
    ((SourceSymplecticAction.CM.ballEmbeddingMatrix K g 1).mulVec (CMExtraction.UnitaryFrameAction.weightedFrame (B.b : ℂ) z.val u).1,
      (SourceSymplecticAction.CM.ballEmbeddingMatrix K g (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)).mulVec (CMExtraction.UnitaryFrameAction.weightedFrame (B.b : ℂ) z.val u).2) =
      CMExtraction.UnitaryFrameAction.weightedFrame (B.b : ℂ) (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val)
        ((sourceActiveFrameMatrix K g hdet B z.val).mulVec u) :=
  CMExtraction.UnitaryFrameAction.weightedFrame_transform (B.b : ℂ) (fun hb => (ne_of_lt B.negative) (by rw [hb]; rfl))
    _ _ (ball_embedding_sl_cross K g hdet B hg) z.val
    (BallLineAction.CM.ball_action_denominator_ne_zero K B g hg z) u

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallFrameMatrices.CM
