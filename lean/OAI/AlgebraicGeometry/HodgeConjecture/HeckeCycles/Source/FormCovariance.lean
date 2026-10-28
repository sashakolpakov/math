import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ThetaVector
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PeriodDifferential

/-! # Form Covariance -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FormCovariance.CM

noncomputable section

/-! Covariance of the source's literal projected theta form, retaining
the exact scalar determined by its half-determinant and line frames.
No theta-map, period, or cotangent identification is assumed. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ThetaVector.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PeriodDifferential.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Projection.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PoissonAutomorphy.CM

universe u v w

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)

theorem theta_vector_annihilator (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places))
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    GeometricSource.CM.localPairing E B.b 1 (GeometricSource.CM.BallDatum.lineVector z) (ThetaVector.CM.thetaVector E L φ z (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)) = 0 := by
  have h := UnitaryEq.CM.PeriodCovariance.graph_prescribed E L z hz
    (Theta.Projection.CM.coefficients (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst φ (L.period z))) places.distinguished
  simp only [places.identity, mul_one] at h
  exact h.2

theorem oneForm_vector (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) (z ξ : GeometricSource.CM.BallChart) :
    RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L) φ z ξ =
      (L.halfDet z : ℂ) * GeometricSource.CM.localPairing E B.b 1 (PeriodDifferential.CM.tangent ξ)
        (ThetaVector.CM.thetaVector E L φ z (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)) := by
  exact Theta.Projection.CM.projection_apply E L z ξ (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst φ (L.period z))

theorem pairing_smul_right (τ : Gal(E/ℚ)) (c : ℂ) (x y : GeometricSource.CM.Vec ℂ) :
    GeometricSource.CM.localPairing E B.b τ x (c • y) = c * GeometricSource.CM.localPairing E B.b τ x y := by
  simp only [GeometricSource.CM.localPairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

def multiplier (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : GeometricSource.CM.BallChart) : ℂ :=
  (L.halfDet (UnitaryEq.CM.Frames.period E g z) : ℂ) *
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)) (L.period z) /
    (PeriodDifferential.CM.lineScale E g z * (L.halfDet z : ℂ))

theorem multiplier_ne_zero (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) : multiplier E L g z ≠ 0 := by
  exact div_ne_zero
    (mul_ne_zero (Units.ne_zero _) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet_ne_zero _ _))
    (mul_ne_zero (PeriodDifferential.CM.lineScale_ne_zero E g z hz) (Units.ne_zero _))

variable {MpR : Type u} {MpF : Type v} {MpA : Type w}
  [Group MpR] [Group MpF] [Group MpA]

theorem oneForm_weighted_covariance (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0, u, v, w})
    (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (GeometricSource.CM.Positions E places) MpR MpF MpA)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) (ξ : GeometricSource.CM.BallChart) :
    (PeriodDifferential.CM.lineScale E g z * (L.halfDet z : ℂ)) *
      RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L)
        (W.finiteAction (ComplexAction.CM.Symplectic.symplectic E L.coordinates g) φ) (UnitaryEq.CM.Frames.period E g z)
        (fderiv ℂ (UnitaryEq.CM.Frames.period E g) z ξ) =
    ((L.halfDet (UnitaryEq.CM.Frames.period E g z) : ℂ) *
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ComplexAction.CM.Symplectic.symplectic E L.coordinates g)) (L.period z)) *
        RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L) φ z ξ := by
  rw [oneForm_vector E L _ (UnitaryEq.CM.Frames.period E g z) (fderiv ℂ (UnitaryEq.CM.Frames.period E g) z ξ),
    oneForm_vector E L φ z ξ, ThetaVector.CM.theta_vector_covariance E L hPoissonAutomorphy W g φ z hz]
  simp only [Pi.smul_apply]
  rw [pairing_smul_right, UnitaryEq.CM.Frames.ambientOperator_apply]
  have h := PeriodDifferential.CM.cotangent_covariance E g z hz ξ (ThetaVector.CM.thetaVector E L φ z (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))
    (theta_vector_annihilator E L φ z hz)
  rw [← h]
  ring

theorem oneForm_covariance (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0, u, v, w})
    (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (GeometricSource.CM.Positions E places) MpR MpF MpA)
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    (RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L)
      (W.finiteAction (ComplexAction.CM.Symplectic.symplectic E L.coordinates g) φ) (UnitaryEq.CM.Frames.period E g z)).comp
        (fderiv ℂ (UnitaryEq.CM.Frames.period E g) z) =
    multiplier E L g z • RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L) φ z := by
  apply ContinuousLinearMap.ext
  intro ξ
  simp only [ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul]
  have hn := mul_ne_zero (PeriodDifferential.CM.lineScale_ne_zero E g z hz) (Units.ne_zero (L.halfDet z))
  apply mul_left_cancel₀ hn
  change (PeriodDifferential.CM.lineScale E g z * (L.halfDet z : ℂ)) * _ =
    (PeriodDifferential.CM.lineScale E g z * (L.halfDet z : ℂ)) *
      (multiplier E L g z * RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L) φ z ξ)
  rw [oneForm_weighted_covariance E L hPoissonAutomorphy W g φ z hz ξ]
  unfold multiplier
  field_simp [PeriodDifferential.CM.lineScale_ne_zero E g z hz]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.FormCovariance.CM
