import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarTheta
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarDeterminant
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.MultiplierSign

/-! # Scalar Family -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarFamily.CM.Family

noncomputable section

/-! The original source theta family has one scalar covariance factor
on the entire connected ball. Both its period and derivative remain
the ones in the source predicate. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.NormOneScalar.CM

universe u v w
variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) (r : Eˣ) (hr : (r : E) * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)

def family : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) →ₗ[ℂ] (B.Domain → GeometricSource.CM.BallChart →L[ℂ] ℂ) :=
  LinearMap.pi (fun z => (LinearMap.proj z.val).comp
    (RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L)))

def halfDeterminant : ℂ := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)) (L.period 0)

theorem continuous : ContinuousOn
    (fun z => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)) (L.period z)) B.domain := by
  have h := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDetExtension_continuousOn (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr))).comp
    L.holomorphic.continuousOn (fun z _ => (show (L.period z).matrix ∈ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.siegelSet (GeometricSource.CM.Positions E places) from
      ⟨(L.period z).symmetric, (L.period z).imaginary_posDef⟩))
  apply h.congr
  intro z _
  simp only [Function.comp_apply, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDetExtension, dite_eq_left
    (show (L.period z).matrix ∈ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.siegelSet (GeometricSource.CM.Positions E places) from
      ⟨(L.period z).symmetric, (L.period z).imaginary_posDef⟩)]
  rfl

theorem constant (z : GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)) (L.period z) = halfDeterminant E L r hr := by
  have hc : IsPreconnected B.domain :=
    (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ball_pathConnected (B.b : ℂ) B.negative).isConnected.isPreconnected
  let f := fun z => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (NormOneScalar.CM.scalar E L.coordinates r hr)) (L.period z)
  have hsq : Set.EqOn (f ^ 2) ((fun _ : GeometricSource.CM.BallChart => f 0) ^ 2) B.domain := by
    intro x hx
    exact (ScalarDeterminant.CM.halfDet_square E r L hr x hx).trans
      (ScalarDeterminant.CM.halfDet_square E r L hr 0
        (MultiplierSign.CM.zero_mem_domain E)).symm
  have he := hc.eq_of_sq_eq (continuous E L r hr) (continuousOn_const (c := f 0)) hsq
    (fun _ => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet_ne_zero _ _) (MultiplierSign.CM.zero_mem_domain E) rfl
  exact he hz

variable {MpR : Type u} {MpF : Type v} {MpA : Type w} [Group MpR] [Group MpF] [Group MpA]
  (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0, u, v, w})
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (GeometricSource.CM.Positions E places) MpR MpF MpA)

include hPoissonAutomorphy in
theorem covariance (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    family E L (W.finiteAction (NormOneScalar.CM.scalar E L.coordinates r hr) φ) =
      (halfDeterminant E L r hr * (r : ℂ)⁻¹) • family E L φ := by
  ext z ξ
  change RepresentationTheory.Theta.Geometric.LinearTheta.thetaOneFormLinear L.period (Theta.Projection.CM.projection E L)
    (W.finiteAction (NormOneScalar.CM.scalar E L.coordinates r hr) φ) z.val ξ = _
  rw [ScalarTheta.CM.projected_covariance E L r hr hPoissonAutomorphy W φ z.val z.property ξ,
    constant E L r hr z.val z.property]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ScalarFamily.CM.Family
