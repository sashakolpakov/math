import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaBallAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaHalf
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HalfFrameScalarComparison

/-! # Theta Oscillator Factor -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaOscillatorFactor.CM

noncomputable section

/-! The actual AdelicTheta oscillator multiplier in source coordinates, obtained
from its natural-line conclusion and the proved half-frame constant. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalFrame.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PeriodDifferential.CM
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) (T : ThetaRationalFrame.CM.Data E L)
  (hT : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification T (Source.GlobalFrames.CM.frames E
    (OppositeCoordinates.CM.coordinates E L.coordinates)))
  (hG : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification T)
  (C : RepresentationTheory.Weil.AdelicSplitting.Characters.Construction.GlobalCharacters (Source.QuadraticConjugation.CM.Field.RealField E)
    (Source.QuadraticConjugation.CM.Field.discriminant E (OppositeCoordinates.CM.coordinates E L.coordinates)) 3 1)
  (D : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings (Source.QuadraticConjugation.CM.Field.RealField E)
    (Source.QuadraticConjugation.CM.Field.discriminant E (OppositeCoordinates.CM.coordinates E L.coordinates)) 3 1
    (Source.QuadraticForms.CM.hermitianForm E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (Source.QuadraticForms.CM.skewForm E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (Source.QuadraticConjugation.CM.Field.discriminant_ne_zero E (OppositeCoordinates.CM.coordinates E L.coordinates)) C
    (Source.GlobalFrames.CM.frames E (OppositeCoordinates.CM.coordinates E L.coordinates)))
  (hO : RepresentationTheory.Theta.Adelic.DataTheta.OscillatorIdentification T
    (Source.GlobalFrames.CM.frames E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (Source.QuadraticConjugation.CM.Field.discriminant_ne_zero E (OppositeCoordinates.CM.coordinates E L.coordinates)) C D)

include hG hO in
theorem natural_line (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : B.Domain) :
    RepresentationTheory.Theta.Adelic.DataTheta.oscillatorFactor T _ _ C D (ThetaArchimedeanAction.CM.rational E L g)
      (Source.BallNormalization.CM.equiv E B z) *
      T.halfFrame (Source.BallNormalization.CM.equiv E B z) /
      T.halfFrame (Source.BallNormalization.CM.equiv E B
        ⟨Source.UnitaryEq.CM.Frames.period E g z.val, Source.UnitaryEq.CM.PrescribedAction.period_preserves E g z.val z.property⟩) =
      Source.PeriodDifferential.CM.lineScale E g z.val := by
  have h := hO.2.2.2.2.2.2.2.2.1 (ThetaArchimedeanAction.CM.rational E L g)
    (Source.BallNormalization.CM.equiv E B z) 1
  change (_ * _ / _) * 1 =
    RepresentationTheory.Theta.Adelic.BallNatural.Factors.naturalHalfFactor 1
      (T.ball (ThetaArchimedeanAction.CM.rational E L g)) (Source.BallNormalization.CM.equiv E B z) * 1 at h
  have hn := (mul_one _).symm.trans (h.trans (mul_one _))
  have hd := congrArg (fun y =>
    RepresentationTheory.Theta.Adelic.DataTheta.oscillatorFactor T _ _ C D (ThetaArchimedeanAction.CM.rational E L g)
      (Source.BallNormalization.CM.equiv E B z) *
      T.halfFrame (Source.BallNormalization.CM.equiv E B z) / T.halfFrame y)
    (ThetaBallAction.CM.action E L T hG g z)
  exact hd.symm.trans (hn.trans (ThetaBallAction.CM.natural_half E L T hG g z))

include hG hO in
theorem source_factor (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : B.Domain) :
    RepresentationTheory.Theta.Adelic.DataTheta.oscillatorFactor T _ _ C D (ThetaArchimedeanAction.CM.rational E L g)
      (Source.BallNormalization.CM.equiv E B z) =
      Source.PeriodDifferential.CM.lineScale E g z.val * (L.halfDet z.val : ℂ) / (L.halfDet (Source.UnitaryEq.CM.Frames.period E g z.val) : ℂ) *
        RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)) (L.period (Source.UnitaryEq.CM.Frames.period E g z.val)) /
        RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)) (L.period z.val) := by
  let z' : B.Domain := ⟨Source.UnitaryEq.CM.Frames.period E g z.val, Source.UnitaryEq.CM.PrescribedAction.period_preserves E g z.val z.property⟩
  exact HalfFrameScalarComparison.CM.ratio
    (T.halfFrame (Source.BallNormalization.CM.equiv E B z))
    (T.halfFrame (Source.BallNormalization.CM.equiv E B z'))
    (L.halfDet z.val : ℂ) (L.halfDet z'.val : ℂ)
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)) (L.period z.val))
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)) (L.period z'.val))
    (ThetaHalf.CM.DeterminantConstant.scalar E L T hT) _ (Source.PeriodDifferential.CM.lineScale E g z.val)
    (hG.2.2.2.2.2.1 (Source.BallNormalization.CM.equiv E B z)).1
    (hG.2.2.2.2.2.1 (Source.BallNormalization.CM.equiv E B z')).1
    (Units.ne_zero _) (Units.ne_zero _) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet_ne_zero _ _)
    (ThetaHalf.CM.DeterminantConstant.scalar_ne_zero E L T hT hG)
    (ThetaHalf.CM.DeterminantConstant.halfFrame_identity E L T hT hG z)
    (ThetaHalf.CM.DeterminantConstant.halfFrame_identity E L T hT hG z')
    (natural_line E L T hG C D hO g z)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaOscillatorFactor.CM
