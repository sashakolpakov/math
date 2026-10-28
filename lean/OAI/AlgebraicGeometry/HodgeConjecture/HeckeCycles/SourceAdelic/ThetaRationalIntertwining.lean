import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalTheta
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaIntrinsicAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaThetaFaithfulness

/-! # Theta Rational Intertwining -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalIntertwining.CM

noncomputable section

/-! Faithfulness of the full theta function identifies the actual native
finite representation with the original source action on every rational element. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalFrame.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PeriodDifferential.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM.Symplectic
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaThetaComparison.CM
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

universe u v w

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) (T : ThetaRationalFrame.CM.Data E L)
  (hT : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification T (Source.GlobalFrames.CM.frames E
    (OppositeCoordinates.CM.coordinates E L.coordinates)))
  (hG : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification T)
  {MpR : Type u} {MpF : Type v} {MpA : Type w} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (GeometricSource.CM.Positions E places) MpR MpF MpA)
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

  (hCov : RepresentationTheory.Theta.Adelic.DataTheta.Descent.RationalHeckeCovariance T
    (Source.GlobalFrames.CM.frames E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (Source.QuadraticConjugation.CM.Field.discriminant_ne_zero E (OppositeCoordinates.CM.coordinates E L.coordinates)) C D)

include hG hO hCov in
theorem functions (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0, u, v, w})
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz (Source.QuadraticConjugation.CM.Field.RealField E) 3
      (ThetaRationalTheta.CM.transformed E L T hT W C D g φ) =
    RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz (Source.QuadraticConjugation.CM.Field.RealField E) 3
      (ThetaThetaComparison.CM.sourceInput E L T hT W (SourceFinite.Hom.CM.finiteAction E L W g φ)) := by
  let z : B.Domain := ⟨0, Source.MultiplierSign.CM.zero_mem_domain E⟩
  exact Adelic.ThetaThetaFaithfulness.CM.functions_eq (Source.QuadraticConjugation.CM.Field.RealField E) T _ _
    (T.period (Source.BallNormalization.CM.equiv E B
      ⟨Source.UnitaryEq.CM.Frames.period E g z.val, Source.UnitaryEq.CM.PrescribedAction.period_preserves E g z.val z.property⟩))
    (ThetaRationalTheta.CM.full_theta E L T hT hG W C D hO hCov hPoissonAutomorphy g φ z)

include hG hO hCov in
theorem action (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0, u, v, w})
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    ThetaIntrinsicAction.CM.Intrinsic.action E L T hT W C D (ThetaRationalTheta.CM.rational E L g) φ =
      SourceFinite.Hom.CM.finiteAction E L W g φ := by
  apply (ThetaFunctionCoordinates.CM.equivalence E L T hT W).injective
  exact (ThetaIntrinsicAction.CM.Intrinsic.tensor_intertwines E L T hT W C D
    (ThetaRationalTheta.CM.rational E L g) φ).trans
      ((functions E L T hT hG W C D hO hCov hPoissonAutomorphy g φ).trans
        (ThetaFunctionCoordinates.CM.source_input_evaluation E L T hT W
          (SourceFinite.Hom.CM.finiteAction E L W g φ)))

include hG hO hCov in
theorem hom (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0, u, v, w}) :
    (ThetaIntrinsicAction.CM.Intrinsic.action E L T hT W C D).comp
      (ThetaRationalTheta.CM.rational E L) = SourceFinite.Hom.CM.finiteAction E L W := by
  apply MonoidHom.ext
  intro g
  apply LinearEquiv.ext
  exact action E L T hT hG W C D hO hCov hPoissonAutomorphy g

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalIntertwining.CM
