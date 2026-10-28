import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceFrameAction
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourcePeriodAction
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.AdaptedTotal

/-! # Source Half Det Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceHalfDetAction.CM

noncomputable section

/-! ThetaCycle: derive the geometric square-root multiplier from the literal
source period, adapted frame, and projective denominator. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsGalois ℚ K]
  [NumberField.IsCMField K] {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Gal(K/ℚ) → Bool}
  (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
  (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y)

theorem source_graph_action (z : B.Domain) (x : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    SourceSymplecticAction.CM.ballAmbientAction K g (HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z.val) x) =
      HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val))
        ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SourceSymplecticAction.CM.sourceBallSymplectic K L.coordinates g hg)).complexify.denominator
          (L.period z.val).matrix *ᵥ x) := by
  apply (SourceSymplecticAction.CM.sourceComplexSumCoordinates K L.coordinates).injective
  rw [← SourceSymplecticAction.CM.source_rational_matrix_complex_action, SourcePeriodAction.CM.source_graph_sum_coordinates,
    SourcePeriodAction.CM.source_graph_sum_coordinates]
  change (SourceSymplecticAction.CM.sourceBallSymplectic K L.coordinates g hg).val.map (algebraMap ℚ ℂ) *ᵥ
    Sum.elim ((L.period z.val).matrix *ᵥ x) x = _
  rw [SourcePeriodAction.CM.source_ball_period_transform K L g hg z]
  exact MovingTotalPeriod.CM.rational_symplectic_graph_substitution (SourceSymplecticAction.CM.sourceBallSymplectic K L.coordinates g hg)
    (L.period z.val) x

def sourceAdaptedGraphMatrix (z : HeckeCycles.GeometricSource.CM.BallChart) : Matrix (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) ℂ :=
  LinearMap.toMatrix' ((HeckeCycles.GeometricSource.CM.adaptedCoordinates K places d).comp
    (HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z)))

omit [IsGalois ℚ K] in
theorem source_adapted_graph_matrix_apply (z : HeckeCycles.GeometricSource.CM.BallChart) (x : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    sourceAdaptedGraphMatrix K L z *ᵥ x =
      HeckeCycles.GeometricSource.CM.adaptedCoordinates K places d (HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z) x) :=
  LinearMap.toMatrix'_mulVec _ _

omit [IsGalois ℚ K] in
theorem source_adapted_graph_matrix_det (z : B.Domain) :
    (sourceAdaptedGraphMatrix K L z.val).det = (L.halfDet z.val : ℂ) ^ 2 := by
  rw [sourceAdaptedGraphMatrix, LinearMap.det_toMatrix']
  exact (L.halfDet_square z.val z.property).symm

variable (hdet : LinearMap.det g.toLinearMap = 1)

theorem source_adapted_graph_action (z : B.Domain) (x : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :
    sourceAdaptedGraphMatrix K L (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val) *ᵥ
        ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SourceSymplecticAction.CM.sourceBallSymplectic K L.coordinates g hg)).complexify.denominator
          (L.period z.val).matrix *ᵥ x) =
      SourceFrameAction.CM.sourceFrameMatrix K g hdet B places d z.val *ᵥ (sourceAdaptedGraphMatrix K L z.val *ᵥ x) := by
  rw [source_adapted_graph_matrix_apply, source_adapted_graph_matrix_apply,
    ← source_graph_action K L g hg z x]
  have hr := AdaptedTotal.CM.native_frame_recovers_line_graph K L z.val z.property x
  calc
    _ = HeckeCycles.GeometricSource.CM.adaptedCoordinates K places d
        (SourceSymplecticAction.CM.ballAmbientAction K g (Prescribed.CM.nativePeriodFrame K B places d z.val
          (HeckeCycles.GeometricSource.CM.adaptedCoordinates K places d (HeckeCycles.GeometricSource.CM.graphInAmbient K L.coordinates (L.period z.val) x)))) :=
      congrArg (fun w => HeckeCycles.GeometricSource.CM.adaptedCoordinates K places d (SourceSymplecticAction.CM.ballAmbientAction K g w)) hr.symm
    _ = _ := by rw [SourceFrameAction.CM.source_native_frame_transform K g hdet B places d hg z, Prescribed.CM.adapted_native_frame]

theorem source_adapted_graph_matrix_action (z : B.Domain) :
    sourceAdaptedGraphMatrix K L (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val) *
        (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SourceSymplecticAction.CM.sourceBallSymplectic K L.coordinates g hg)).complexify.denominator
          (L.period z.val).matrix =
      SourceFrameAction.CM.sourceFrameMatrix K g hdet B places d z.val * sourceAdaptedGraphMatrix K L z.val := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  simp only [← Matrix.mulVec_mulVec]
  exact source_adapted_graph_action K L g hg hdet z x

include hdet in
theorem source_half_det_transform_square (z : B.Domain) :
    (L.halfDet (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val) : ℂ) ^ 2 *
        ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SourceSymplecticAction.CM.sourceBallSymplectic K L.coordinates g hg)).complexify.denominator
          (L.period z.val).matrix).det =
      ((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2) ^ 2 *
        (L.halfDet z.val : ℂ) ^ 2 := by
  have he := congrArg Matrix.det (source_adapted_graph_matrix_action K L g hg hdet z)
  rw [Matrix.det_mul, Matrix.det_mul, SourceFrameAction.CM.source_frame_matrix_det K g hdet B places d hg z.val,
    source_adapted_graph_matrix_det K L z,
    source_adapted_graph_matrix_det K L
      ⟨HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val, BallLineAction.CM.ball_line_action_mem K B g hg z⟩] at he
  exact he

def sourceGeometricMultiplier (z : HeckeCycles.GeometricSource.CM.BallChart) : ℂ :=
  ((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z) 2) *
    (L.halfDet z : ℂ) / (L.halfDet (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z) : ℂ)

include hdet in
theorem source_geometric_multiplier_square (z : B.Domain) :
    sourceGeometricMultiplier K L g z.val ^ 2 =
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (SourceSymplecticAction.CM.sourceBallSymplectic K L.coordinates g hg)).complexify.denominator
        (L.period z.val).matrix).det := by
  have he := source_half_det_transform_square K L g hg hdet z
  have hn := (L.halfDet (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val)).ne_zero
  apply (mul_right_cancel₀ (pow_ne_zero 2 hn))
  calc
    _ = ((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2) ^ 2 *
        (L.halfDet z.val : ℂ) ^ 2 := by
      unfold sourceGeometricMultiplier
      field_simp
    _ = _ := he.symm.trans (mul_comm _ _)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceHalfDetAction.CM
