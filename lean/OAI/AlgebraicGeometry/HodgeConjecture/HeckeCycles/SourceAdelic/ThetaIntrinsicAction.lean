import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaFunctionCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaFiniteFunctionAction
import OAI.RepresentationTheory.Hecke.RadialDilation.TensorCommutant

/-! # Theta Intrinsic Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaIntrinsicAction.CM.Intrinsic

noncomputable section

/-! Transport AdelicTheta's actual supplied finite representation to the original
source Schwartz space through the derived input equivalence. The action
is smooth and its tensor evaluation identity is exact. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalFrame.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticForms.CM
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.Data

universe u v w

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) (T : ThetaRationalFrame.CM.Data E L)
  (hT : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification T (Source.GlobalFrames.CM.frames E
    (OppositeCoordinates.CM.coordinates E L.coordinates)))
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

def action : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (Source.QuadraticConjugation.CM.Field.RealField E) (Source.QuadraticForms.CM.hermitianForm E (OppositeCoordinates.CM.coordinates E L.coordinates)) →*
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ] RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :=
  (RepresentationTheory.Hecke.RadialDilation.TensorCommutant.Realization.conjugateLinearAut
    (ThetaFunctionCoordinates.CM.equivalence E L T hT W).symm).comp
      (Adelic.ThetaFiniteFunctionAction.CM.action (Source.QuadraticConjugation.CM.Field.RealField E) _ 1 _ _ _ C _ D)

theorem intertwines
    (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (Source.QuadraticConjugation.CM.Field.RealField E) (Source.QuadraticForms.CM.hermitianForm E (OppositeCoordinates.CM.coordinates E L.coordinates)))
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    ThetaFunctionCoordinates.CM.equivalence E L T hT W (action E L T hT W C D g φ) =
      Adelic.ThetaFiniteFunctionAction.CM.action (Source.QuadraticConjugation.CM.Field.RealField E) _ 1 _ _ _ C _ D g
        (ThetaFunctionCoordinates.CM.equivalence E L T hT W φ) :=
  (ThetaFunctionCoordinates.CM.equivalence E L T hT W).apply_symm_apply _

theorem tensor_intertwines
    (g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (Source.QuadraticConjugation.CM.Field.RealField E) (Source.QuadraticForms.CM.hermitianForm E (OppositeCoordinates.CM.coordinates E L.coordinates)))
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    ThetaFunctionCoordinates.CM.equivalence E L T hT W (action E L T hT W C D g φ) =
      RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz (Source.QuadraticConjugation.CM.Field.RealField E) 3
        (RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteAction (Source.QuadraticConjugation.CM.Field.RealField E) _ _ _ C _ D g
          (ThetaThetaComparison.CM.sourceInput E L T hT W φ)) := by
  exact (intertwines E L T hT W C D g φ).trans ((congrArg (Adelic.ThetaFiniteFunctionAction.CM.action (Source.QuadraticConjugation.CM.Field.RealField E)
    (Source.QuadraticConjugation.CM.Field.discriminant E (OppositeCoordinates.CM.coordinates E L.coordinates)) 1
    (Source.QuadraticForms.CM.hermitianForm E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (Source.QuadraticForms.CM.skewForm E (OppositeCoordinates.CM.coordinates E L.coordinates))
    (Source.QuadraticConjugation.CM.Field.discriminant_ne_zero E (OppositeCoordinates.CM.coordinates E L.coordinates)) C
    (Source.GlobalFrames.CM.frames E (OppositeCoordinates.CM.coordinates E L.coordinates)) D g)
      (ThetaFunctionCoordinates.CM.source_input_evaluation E L T hT W φ).symm).trans
    (Adelic.ThetaFiniteFunctionAction.CM.intertwines (Source.QuadraticConjugation.CM.Field.RealField E)
      (Source.QuadraticConjugation.CM.Field.discriminant E (OppositeCoordinates.CM.coordinates E L.coordinates)) 1
      (Source.QuadraticForms.CM.hermitianForm E (OppositeCoordinates.CM.coordinates E L.coordinates))
      (Source.QuadraticForms.CM.skewForm E (OppositeCoordinates.CM.coordinates E L.coordinates))
      (Source.QuadraticConjugation.CM.Field.discriminant_ne_zero E (OppositeCoordinates.CM.coordinates E L.coordinates)) C
      (Source.GlobalFrames.CM.frames E (OppositeCoordinates.CM.coordinates E L.coordinates)) D g
      (ThetaThetaComparison.CM.sourceInput E L T hT W φ)))

theorem smooth (hD : RepresentationTheory.Theta.Adelic.Data.FiniteConclusion (Source.QuadraticConjugation.CM.Field.RealField E) _ 3 1 _ _ _ C _ D)
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    IsOpen {g : RepresentationTheory.Theta.Adelic.FiniteSchwartz.FiniteSU (Source.QuadraticConjugation.CM.Field.RealField E)
      (Source.QuadraticForms.CM.hermitianForm E (OppositeCoordinates.CM.coordinates E L.coordinates)) |
        action E L T hT W C D g φ = φ} :=
  SurjectiveRepresentationSmoothness.CM.conjugate_smooth
    (ThetaFunctionCoordinates.CM.equivalence E L T hT W)
    (Adelic.ThetaFiniteFunctionAction.CM.action (Source.QuadraticConjugation.CM.Field.RealField E) _ 1 _ _ _ C _ D)
    (Adelic.ThetaFiniteFunctionAction.CM.smooth (Source.QuadraticConjugation.CM.Field.RealField E) _ 1 _ _ _ C _ D hD) φ

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaIntrinsicAction.CM.Intrinsic
