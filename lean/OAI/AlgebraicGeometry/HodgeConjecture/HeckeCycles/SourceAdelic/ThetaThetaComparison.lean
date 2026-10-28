import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaPeriodComparison
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaThetaCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Reindex
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PoissonAutomorphy

/-! # Theta Theta Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaThetaComparison.CM

noncomputable section

/-! The actual AdelicTheta tensor input obtained from an original source finite
input has the original source theta series, with exactly PoissonAutomorphy's proved
symplectic Gaussian factor and the derived source period change. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalFrame.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

universe u v w

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) (T : ThetaRationalFrame.CM.Data E L)
  (hT : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification T (Source.GlobalFrames.CM.frames E
    (OppositeCoordinates.CM.coordinates E L.coordinates)))
  (hG : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification T)

def input : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) →ₗ[ℂ]
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (Source.QuadraticConjugation.CM.Field.RealField E) 3 :=
  (Adelic.ThetaThetaCoordinates.CM.sectionMap (Source.QuadraticConjugation.CM.Field.RealField E) T).comp
    (Finite.ReindexHeisenberg.CM.Pairing.testEquiv (ThetaRationalFrame.CM.index E L)).toLinearMap

include hG in
theorem theta (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) (z : B.Domain)
    (ξ : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex (Source.BallArithmetic.CM.data E L) → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta T (input E L T φ) (T.period (Source.BallNormalization.CM.equiv E B z)).matrix ξ =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta φ ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)).transformSiegel (L.period z.val))
        (ξ ∘ ThetaRationalFrame.CM.index E L) := by
  change RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta T (Adelic.ThetaThetaCoordinates.CM.sectionMap (Source.QuadraticConjugation.CM.Field.RealField E) T
    (Finite.ReindexHeisenberg.CM.Pairing.testEquiv (ThetaRationalFrame.CM.index E L) φ)) _ _ = _
  rw [Adelic.ThetaThetaCoordinates.CM.section_theta]
  exact Theta.Reindex.CM.theta (ThetaRationalFrame.CM.index E L) φ _ _
    (ThetaPeriodComparison.CM.period_matrix E L T hT hG z) ξ

variable {MpR : Type u} {MpF : Type v} {MpA : Type w} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (GeometricSource.CM.Positions E places) MpR MpF MpA)

def sourceInput : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) →ₗ[ℂ]
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (Source.QuadraticConjugation.CM.Field.RealField E) 3 :=
  (input E L T).comp (W.finiteAction (ThetaRationalFrame.CM.matrix E L T hT)).toLinearMap

def variableChange (z : B.Domain) (ξ : GeometricSource.CM.Positions E places → ℂ) :
    RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex (Source.BallArithmetic.CM.data E L) → ℂ :=
  fun j => (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)).jacobiChange (L.period z.val) ξ ((ThetaRationalFrame.CM.index E L).symm j)

include hG in
theorem source_theta (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0, u, v, w})
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) (z : B.Domain) (ξ : GeometricSource.CM.Positions E places → ℂ) :
    RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta T (sourceInput E L T hT W φ)
      (T.period (Source.BallNormalization.CM.equiv E B z)).matrix (variableChange E L T hT z ξ) =
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)) (L.period z.val) *
        (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)) (L.period z.val) ξ *
          RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta φ (L.period z.val) ξ) := by
  change RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta T (input E L T (W.finiteAction (ThetaRationalFrame.CM.matrix E L T hT) φ)) _ _ = _
  rw [theta E L T hT hG]
  have hv : variableChange E L T hT z ξ ∘ ThetaRationalFrame.CM.index E L =
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)).jacobiChange (L.period z.val) ξ := by
    funext i
    exact congrArg ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)).jacobiChange (L.period z.val) ξ)
      ((ThetaRationalFrame.CM.index E L).symm_apply_apply i)
  rw [hv]
  exact (hPoissonAutomorphy W (ThetaRationalFrame.CM.matrix E L T hT)).2.2.2.2 φ (L.period z.val) ξ

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaThetaComparison.CM
