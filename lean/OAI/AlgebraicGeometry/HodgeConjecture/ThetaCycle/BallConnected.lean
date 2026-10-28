import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Cm
import Mathlib.Analysis.Convex.PathConnected

/-! # Ball Connected -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallConnected.CM

noncomputable section

/-! Connectedness of the actual ball domain and its surjective quotients. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable {K : IntermediateField ℚ ℂ} [NumberField K] [NumberField.IsCMField K]

theorem ball_domain_starConvex (B : HeckeCycles.GeometricSource.CM.BallDatum K) :
    StarConvex ℝ (0 : HeckeCycles.GeometricSource.CM.BallChart) B.domain := by
  intro z hz a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  have hb2 : b * b ≤ 1 := by nlinarith
  have hq : 0 ≤ Complex.normSq (z 0) + Complex.normSq (z 1) :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  change Complex.normSq ((a • 0 + b • z) 0) +
    Complex.normSq ((a • 0 + b • z) 1) < -(B.b : ℂ).re
  simp only [smul_zero, zero_add, Pi.smul_apply, Complex.real_smul,
    Complex.normSq_mul, Complex.normSq_ofReal]
  calc
    _ = (b * b) * (Complex.normSq (z 0) + Complex.normSq (z 1)) := by ring
    _ ≤ Complex.normSq (z 0) + Complex.normSq (z 1) := mul_le_of_le_one_left hq hb2
    _ < -(B.b : ℂ).re := hz

theorem ball_domain_connected (B : HeckeCycles.GeometricSource.CM.BallDatum K) : ConnectedSpace B.Domain := by
  have hz : (0 : HeckeCycles.GeometricSource.CM.BallChart) ∈ B.domain := by
    change Complex.normSq 0 + Complex.normSq 0 < -(B.b : ℂ).re
    simpa only [Complex.normSq_zero, zero_add] using neg_pos.mpr B.negative
  exact Subtype.connectedSpace ((ball_domain_starConvex B).isPathConnected hz).isConnected

theorem principal_quotient_preconnected
    (B : HeckeCycles.GeometricSource.CM.BallDatum K) (N : ℕ) (S : Cm.PrincipalBallSurface K B N) :
    PreconnectedSpace S.surface.variety.analyticSpace := by
  let : ConnectedSpace B.Domain := ball_domain_connected B
  apply preconnectedSpace_iff_univ.mpr
  simpa only [Set.image_univ, S.isBallCover.2.1.range_eq] using
    isPreconnected_univ.image S.projection S.isBallCover.2.2.1.continuous.continuousOn

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallConnected.CM
