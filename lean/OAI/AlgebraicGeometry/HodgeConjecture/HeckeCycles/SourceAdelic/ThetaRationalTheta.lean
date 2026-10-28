import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaJacobiComparison
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaOscillatorFactor
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ThetaFactor
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.ScalarComparison
import OAI.RepresentationTheory.Theta.Adelic.DataTheta
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FunctionSurjectiveExt

/-! # Theta Rational Theta -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalTheta.CM

noncomputable section

/-! Full native rational theta covariance agrees exactly with the actual
source finite action, after the derived frame and input comparisons. -/

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

def rational : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b →*
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (Source.QuadraticConjugation.CM.Field.RealField E)
      (Source.QuadraticForms.CM.hermitianForm E (OppositeCoordinates.CM.coordinates E L.coordinates)) :=
  (RepresentationTheory.Theta.Adelic.RationalSU.rationalFiniteSU (Source.QuadraticConjugation.CM.Field.RealField E) _).comp
    (Source.UnitaryMatrix.CM.hom E (OppositeCoordinates.CM.coordinates E L.coordinates))

def transformed (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (Source.QuadraticConjugation.CM.Field.RealField E) 3 :=
  RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteAction (Source.QuadraticConjugation.CM.Field.RealField E) _ _ _ C _ D (rational E L g)
    (ThetaThetaComparison.CM.sourceInput E L T hT W φ)

include hG hO hCov in
theorem at_variable (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0, u, v, w})
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places))
    (z : B.Domain) (ξ : GeometricSource.CM.Positions E places → ℂ) :
    let z' : B.Domain := ⟨Source.UnitaryEq.CM.Frames.period E g z.val, Source.UnitaryEq.CM.PrescribedAction.period_preserves E g z.val z.property⟩
    let ξ' := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (Source.ComplexAction.CM.Symplectic.symplectic E L.coordinates g)).jacobiChange (L.period z.val) ξ
    RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta T (transformed E L T hT W C D g φ)
      (T.period (Source.BallNormalization.CM.equiv E B z')).matrix (ThetaThetaComparison.CM.variableChange E L T hT z' ξ') =
    RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta T (ThetaThetaComparison.CM.sourceInput E L T hT W (SourceFinite.Hom.CM.finiteAction E L W g φ))
      (T.period (Source.BallNormalization.CM.equiv E B z')).matrix (ThetaThetaComparison.CM.variableChange E L T hT z' ξ') := by
  let z' : B.Domain := ⟨Source.UnitaryEq.CM.Frames.period E g z.val, Source.UnitaryEq.CM.PrescribedAction.period_preserves E g z.val z.property⟩
  let ξ' := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (Source.ComplexAction.CM.Symplectic.symplectic E L.coordinates g)).jacobiChange (L.period z.val) ξ
  let S := ThetaRationalFrame.CM.matrix E L T hT
  let s₀ := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks S) (L.period z.val)
  let s₁ := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks S) (L.period z'.val)
  let q₀ := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks S) (L.period z.val) ξ
  let q₁ := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks S) (L.period z'.val) ξ'
  let c := Source.PeriodDifferential.CM.lineScale E g z.val * (L.halfDet z.val : ℂ) / (L.halfDet z'.val : ℂ)
  let qn := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor (T.symplectic (ThetaArchimedeanAction.CM.rational E L g))
    (T.period (Source.BallNormalization.CM.equiv E B z)) (ThetaThetaComparison.CM.variableChange E L T hT z ξ)
  let qs := RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.quadraticFactor (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (Source.ComplexAction.CM.Symplectic.symplectic E L.coordinates g)) (L.period z.val) ξ
  let a := RepresentationTheory.Theta.Adelic.DataTheta.oscillatorFactor T _ _ C D (ThetaArchimedeanAction.CM.rational E L g)
    (Source.BallNormalization.CM.equiv E B z)
  have hn := (hCov (Source.UnitaryMatrix.CM.hom E
    (OppositeCoordinates.CM.coordinates E L.coordinates) g) (ThetaThetaComparison.CM.sourceInput E L T hT W φ)).1
      (Source.BallNormalization.CM.equiv E B z) (ThetaThetaComparison.CM.variableChange E L T hT z ξ)
  have hargs := congrArg₂ (fun b η =>
    RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta T (transformed E L T hT W C D g φ) (T.period b).matrix η)
    (ThetaBallAction.CM.action E L T hG g z)
    (ThetaJacobiComparison.CM.jacobi E L T hT hG g z ξ)
  have hold := congrArg (fun t : ℂ => a * (qn * t))
    (ThetaThetaComparison.CM.source_theta E L T hT hG W hPoissonAutomorphy φ z ξ)
  have halgebra := Theta.ScalarComparison.CM.covariance a c s₀ s₁ q₀ q₁ qn qs
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.theta φ (L.period z.val) ξ) (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet_ne_zero _ _)
    (ThetaOscillatorFactor.CM.source_factor E L T hT hG C D hO g z)
    (ThetaJacobiComparison.CM.quadratic E L T hT hG g z ξ)
  have hnew := ThetaThetaComparison.CM.source_theta E L T hT hG W hPoissonAutomorphy
    (SourceFinite.Hom.CM.finiteAction E L W g φ) z' ξ'
  have hsource := congrArg (fun t : ℂ => s₁ * (q₁ * t))
    (Source.ThetaFactor.CM.theta E L W hPoissonAutomorphy g φ z.val z.property ξ)
  exact hargs.symm.trans (hn.trans (hold.trans (halgebra.trans (hnew.trans hsource).symm)))

include hG hO hCov in
theorem full_theta (hPoissonAutomorphy : PoissonAutomorphy.CM.PoissonAutomorphyInput.{0, u, v, w})
    (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) (z : B.Domain) :
    let z' : B.Domain := ⟨Source.UnitaryEq.CM.Frames.period E g z.val, Source.UnitaryEq.CM.PrescribedAction.period_preserves E g z.val z.property⟩
    RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta T (transformed E L T hT W C D g φ)
      (T.period (Source.BallNormalization.CM.equiv E B z')).matrix =
    RepresentationTheory.Theta.Adelic.DataTheta.rationalTheta T (ThetaThetaComparison.CM.sourceInput E L T hT W (SourceFinite.Hom.CM.finiteAction E L W g φ))
      (T.period (Source.BallNormalization.CM.equiv E B z')).matrix := by
  let z' : B.Domain := ⟨Source.UnitaryEq.CM.Frames.period E g z.val, Source.UnitaryEq.CM.PrescribedAction.period_preserves E g z.val z.property⟩
  exact FunctionSurjectiveExt.CM.of_two (ThetaThetaComparison.CM.variableChange E L T hT z')
    ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (Source.ComplexAction.CM.Symplectic.symplectic E L.coordinates g)).jacobiChange (L.period z.val))
    (ThetaJacobiComparison.CM.variable_surjective E L T hT z')
    (SymplecticConjugation.CM.jacobi_surjective
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (Source.ComplexAction.CM.Symplectic.symplectic E L.coordinates g)) (L.period z.val)) _ _
    (at_variable E L T hT hG W C D hO hCov hPoissonAutomorphy g φ z)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalTheta.CM
