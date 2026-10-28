import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallFrameMatrices
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectiveCotangent

/-! # Ball Projective Cotangent -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallProjectiveCotangent.CM

noncomputable section

/-! ThetaCycle: the weighted conjugate-component frame induces the actual
cotangent pullback for the specified ball and its projective action. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectiveCotangent.Frame
open OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsGalois ℚ K]
  [NumberField.IsCMField K] (B : HeckeCycles.GeometricSource.CM.BallDatum K)
  (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hdet : LinearMap.det g.toLinearMap = 1)
  (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y)

include hg in
theorem source_ball_projective_cotangent (z : B.Domain) (c ξ : Fin 2 → ℂ) :
    ((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2) *
      CMExtraction.FrameProjection.Multiplicity.coordinateCovector
        (CMExtraction.UnitaryFrameAction.weightedDualCoordinates (B.b : ℂ) (BallFrameMatrices.CM.ballEmbeddingSL K g hdet (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)) z.val *ᵥ c)
        (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val ξ) = CMExtraction.FrameProjection.Multiplicity.coordinateCovector c ξ := by
  have hf : DifferentiableAt ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val :=
    (BallLineAction.CM.ball_line_action_holomorphic K B g hg z.val z.property).differentiableAt
      (B.domain_isOpen.mem_nhds z.property)
  exact CMExtraction.ProjectiveCotangent.Frame.weighted_cotangent (B.b : ℂ)
    (fun hb => (ne_of_lt B.negative) (by rw [hb]; rfl))
    (BallFrameMatrices.CM.ballEmbeddingSL K g hdet 1) (BallFrameMatrices.CM.ballEmbeddingSL K g hdet (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K))
    (BallFrameMatrices.CM.ball_embedding_sl_cross K g hdet B hg) B.domain B.domain_isOpen z.val z.property
    (fun y hy => BallLineAction.CM.ball_action_denominator_ne_zero K B g hg ⟨y, hy⟩)
    (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) hf (fun y _ => (BallFrameMatrices.CM.ball_embedding_sl_chart K g hdet y).symm) c ξ

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallProjectiveCotangent.CM
