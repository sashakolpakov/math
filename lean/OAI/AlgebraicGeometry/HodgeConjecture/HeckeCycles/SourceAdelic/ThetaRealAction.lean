import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaArchimedeanAction

/-! # Theta Real Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRealAction.CM

noncomputable section

/-! The actual archimedean symplectic matrices supplied by AdelicTheta are
the scalar extensions of the derived rational change of source frame. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalFrame.CM
open OAI.RepresentationTheory.Theta.Adelic.DataTheta

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) (T : ThetaRationalFrame.CM.Data E L)
  (hT : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification T (Source.GlobalFrames.CM.frames E
    (OppositeCoordinates.CM.coordinates E L.coordinates)))

theorem matrix_eq (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) :
    (RepresentationTheory.Theta.Adelic.DataTheta.blockMatrix (T.symplectic (ThetaArchimedeanAction.CM.rational E L g))).submatrix
      ((ThetaRationalFrame.CM.index E L).sumCongr (ThetaRationalFrame.CM.index E L)) ((ThetaRationalFrame.CM.index E L).sumCongr (ThetaRationalFrame.CM.index E L)) =
        RepresentationTheory.Theta.Adelic.DataTheta.blockMatrix (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT *
          Source.ComplexAction.CM.Symplectic.symplectic E L.coordinates g * (ThetaRationalFrame.CM.matrix E L T hT)⁻¹)) := by
  have ha := hT.2.2.2.2.2.2.2.2.2
    (Source.UnitaryMatrix.CM.hom E (OppositeCoordinates.CM.coordinates E L.coordinates) g)
  have hq := ThetaRationalAction.CM.matrix_eq E L T hT g
  have hr := congrArg (fun M => M.map (algebraMap ℚ ℝ)) hq
  have he := congrArg (fun M : Matrix
    (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex (Source.BallArithmetic.CM.data E L) ⊕
      RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex (Source.BallArithmetic.CM.data E L))
    (RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex (Source.BallArithmetic.CM.data E L) ⊕
      RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex (Source.BallArithmetic.CM.data E L)) ℝ =>
        M.submatrix ((ThetaRationalFrame.CM.index E L).sumCongr (ThetaRationalFrame.CM.index E L)) ((ThetaRationalFrame.CM.index E L).sumCongr (ThetaRationalFrame.CM.index E L))) ha
  refine he.trans (hr.trans ?_)
  exact (Matrix.fromBlocks_toBlocks _).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRealAction.CM
