import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaThetaComparison
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.FunctionAction

/-! # Theta Function Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaFunctionCoordinates.CM

noncomputable section

/-! The explicit source-to-AdelicTheta input construction is an equivalence on
actual finite Schwartz functions. Its restricted-tensor representative
evaluates to precisely that equivalence. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalFrame.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.QuadraticConjugation.CM.Field
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz

universe u v w

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) (T : ThetaRationalFrame.CM.Data E L)
  (hT : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification T (Source.GlobalFrames.CM.frames E
    (OppositeCoordinates.CM.coordinates E L.coordinates)))
  {MpR : Type u} {MpF : Type v} {MpA : Type w} [Group MpR] [Group MpF] [Group MpA]
  (W : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.WeilData (GeometricSource.CM.Positions E places) MpR MpF MpA)

def equivalence : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places) ≃ₗ[ℂ] RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.adelicSchwartzFunctions (Source.QuadraticConjugation.CM.Field.RealField E) 3 :=
  ((W.finiteAction (ThetaRationalFrame.CM.matrix E L T hT)).trans (Finite.ReindexHeisenberg.CM.Pairing.testEquiv (ThetaRationalFrame.CM.index E L))).trans
    (Finite.RationalPositionCoordinates.CM.equivalence (Source.QuadraticConjugation.CM.Field.RealField E) 3 T.rationalPosition)

theorem source_input_evaluation (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places)) :
    RepresentationTheory.Theta.Adelic.CompactSupport.AdelicSchwartz.toAdelicSchwartz (Source.QuadraticConjugation.CM.Field.RealField E) 3 (ThetaThetaComparison.CM.sourceInput E L T hT W φ) =
      equivalence E L T hT W φ :=
  Finite.FunctionAction.CM.section_identity (Source.QuadraticConjugation.CM.Field.RealField E) 3 (equivalence E L T hT W φ)

theorem source_input_values (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (GeometricSource.CM.Positions E places))
    (x : Fin 3 → RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.FiniteAdeles (Source.QuadraticConjugation.CM.Field.RealField E)) :
    RepresentationTheory.Theta.Adelic.Evaluation.finiteSchwartzFunction (Source.QuadraticConjugation.CM.Field.RealField E) 3
      (ThetaThetaComparison.CM.sourceInput E L T hT W φ) x =
        (equivalence E L T hT W φ).val x :=
  congrFun (congrArg Subtype.val (source_input_evaluation E L T hT W φ)) x

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaFunctionCoordinates.CM
