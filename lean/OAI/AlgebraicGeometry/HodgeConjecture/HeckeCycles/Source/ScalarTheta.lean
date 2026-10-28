import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarDeterminant
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ThetaVector

/-! # Scalar Theta -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarTheta.CM

noncomputable section

/-! PoissonAutomorphy gives the scalar covariance of the original projected theta
derivative at its fixed source period. Its character is derived from
the actual conjugate embedding of norm-one multiplication. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.NormOneScalar.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarDeterminant.CM.Period
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Projection.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ThetaVector.CM

universe u v w
variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) (r : Eˣ) (hr : (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
  {MpR : Type u} {MpF : Type v} {MpA : Type w} [Group MpR] [Group MpF] [Group MpA]
  (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0, u, v, w}) (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (GeometricSource.CM.Positions E places) MpR MpF MpA)

include hPoissonAutomorphy in
theorem first_covariance (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places))
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst (W.finiteAction (NormOneScalar.CM.scalar E L.coordinates r hr) φ) (L.period z)).comp
        ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)).jacobiChange (L.period z)) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)) (L.period z) • RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst φ (L.period z) := by
  have h := RepresentationTheory.Theta.Geometric.LinearTheta.canonical_first_covariance W (NormOneScalar.CM.scalar E L.coordinates r hr)
    (hPoissonAutomorphy W (NormOneScalar.CM.scalar E L.coordinates r hr)).2.2.2.2 φ (L.period z)
  rw [← ScalarDeterminant.CM.Period.period_fixed E L r hr z hz] at h
  exact h

include hPoissonAutomorphy in
theorem coefficient_covariance (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places))
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    Theta.Projection.CM.coefficients (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst (W.finiteAction (NormOneScalar.CM.scalar E L.coordinates r hr) φ) (L.period z)) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)) (L.period z) •
        (((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)).complexify.denominator
          (L.period z).matrix).mulVec (Theta.Projection.CM.coefficients (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst φ (L.period z)))) := by
  apply DerivativeCoordinates.CM.coefficients_of_covariance
    _ _ _ _ ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)).denominator_det_isUnit (L.period z))
  exact first_covariance E L r hr hPoissonAutomorphy W φ z hz

include hPoissonAutomorphy in
theorem vector_covariance (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places))
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    ThetaVector.CM.thetaVector E L (W.finiteAction (NormOneScalar.CM.scalar E L.coordinates r hr) φ) z =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)) (L.period z) •
        NormOneScalar.CM.ambient E r (ThetaVector.CM.thetaVector E L φ z) := by
  unfold ThetaVector.CM.thetaVector
  rw [coefficient_covariance E L r hr hPoissonAutomorphy W φ z hz, map_smul, ScalarDeterminant.CM.Period.graph_action E L r hr z hz]

include hr in
theorem conjugate_eq_inverse : ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = (r : E)⁻¹ := by
  apply mul_left_cancel₀ (Units.ne_zero r)
  rw [hr, mul_inv_cancel₀ (Units.ne_zero r)]

include hPoissonAutomorphy in
theorem projected_covariance (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places))
    (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) (ξ : GeometricSource.CM.BallChart) :
    RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L) (W.finiteAction (NormOneScalar.CM.scalar E L.coordinates r hr) φ) z ξ =
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)) (L.period z) * (r : ℂ)⁻¹) *
        RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L) φ z ξ := by
  change Theta.Projection.CM.projection E L z (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst (W.finiteAction (NormOneScalar.CM.scalar E L.coordinates r hr) φ) (L.period z)) ξ = _
  rw [Theta.Projection.CM.projection_apply]
  change (L.halfDet z : ℂ) * GeometricSource.CM.localPairing E B.b 1 ![ξ 0, ξ 1, 0]
    (ThetaVector.CM.thetaVector E L (W.finiteAction (NormOneScalar.CM.scalar E L.coordinates r hr) φ) z (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)) = _
  rw [vector_covariance E L r hr hPoissonAutomorphy W φ z hz]
  change (L.halfDet z : ℂ) * GeometricSource.CM.localPairing E B.b 1 ![ξ 0, ξ 1, 0]
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)) (L.period z) •
      (((ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) : E) : ℂ) • ThetaVector.CM.thetaVector E L φ z (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))) = _
  rw [ScalarDeterminant.CM.Period.pairing_smul_right, ScalarDeterminant.CM.Period.pairing_smul_right, conjugate_eq_inverse E r hr]
  change _ = (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)) (L.period z) * (r : ℂ)⁻¹) *
    Theta.Projection.CM.projection E L z (RepresentationTheory.Theta.Geometric.LinearTheta.canonicalFirst φ (L.period z)) ξ
  rw [Theta.Projection.CM.projection_apply]
  simp only [IntermediateField.coe_inv]
  change _ = (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)) (L.period z) * (r : ℂ)⁻¹) *
    ((L.halfDet z : ℂ) * GeometricSource.CM.localPairing E B.b 1 ![ξ 0, ξ 1, 0]
      (ThetaVector.CM.thetaVector E L φ z (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)))
  ring

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarTheta.CM
