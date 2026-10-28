import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaArchimedeanAction
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaDistinguishedBasis
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalFrame
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.PeriodDifferential

/-! # Theta Ball Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaBallAction.CM

noncomputable section

/-! The actual AdelicTheta ball action of the rational source group is exactly
the source projective action conjugated by the proved ball normalization. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.BallNormalization.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.Frames
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates

theorem chart_of_line (g : Matrix.SpecialLinearGroup (Fin 3) ℂ) (z y : Fin 2 → ℂ) (c : ℂ)
    (hc : c ≠ 0) (h : g.val.mulVec (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z) = c • RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector y) : RepresentationTheory.Theta.Adelic.DeterminantCoordinates.chartImage g z = y := by
  have hd : RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator g z = c := by simpa [RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator, RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector] using congrFun h 2
  funext i
  change g.val.mulVec (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector z) i.castSucc / RepresentationTheory.Theta.Adelic.DeterminantCoordinates.denominator g z = y i
  rw [hd]
  apply (div_eq_iff hc).mpr
  have hi := congrFun h i.castSucc
  fin_cases i <;> simpa [RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector, mul_comm] using hi

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)

theorem line_action (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : B.Domain) :
    (RepresentationTheory.Theta.Adelic.BallGeometryData.standardMatrix (Source.BallArithmetic.CM.data E L)
        (ThetaArchimedeanAction.CM.rational E L g) places.distinguished).mulVec
        (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector (Source.BallNormalization.CM.normalize E B z.val)) =
          Source.PeriodDifferential.CM.lineScale E g z.val • RepresentationTheory.Theta.Adelic.DeterminantCoordinates.lineVector (Source.BallNormalization.CM.normalize E B (Source.UnitaryEq.CM.Frames.period E g z.val)) := by
  let c := Source.PeriodDifferential.CM.lineScale E g z.val
  have hl := Source.PeriodDifferential.CM.line_scale_action E g z.val z.property
  change _ = c • _
  rw [ThetaArchimedeanAction.CM.standard_matrix, ReferenceDatum.CM.embeddings_distinguished]
  change (g.val.val.map E.val).mulVec (GeometricSource.CM.BallDatum.lineVector z.val) =
    c • GeometricSource.CM.BallDatum.lineVector (Source.UnitaryEq.CM.Frames.period E g z.val) at hl
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    ThetaDistinguishedBasis.CM.inverse_line_coordinates,
    Matrix.mulVec_smul]
  refine (congrArg (fun v : GeometricSource.CM.Vec ℂ =>
    (Source.ArchimedeanBases.CM.hermitian E (B := B) places.distinguished).inv.mulVec
      ((Source.BallNormalization.CM.radius E B : ℂ)⁻¹ • v)) hl).trans ?_
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, ThetaDistinguishedBasis.CM.line_coordinates]
  funext i
  change (Source.BallNormalization.CM.radius E B : ℂ)⁻¹ * (c * ((Source.BallNormalization.CM.radius E B : ℂ) * _)) = c * _
  have hr := Complex.ofReal_ne_zero.mpr (Source.BallNormalization.CM.radius_ne_zero E B)
  field_simp

variable (T : ThetaRationalFrame.CM.Data E L) (hG : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification T)

include hG in
theorem action (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : B.Domain) :
    T.ball (ThetaArchimedeanAction.CM.rational E L g) • (Source.BallNormalization.CM.equiv E B z) =
      Source.BallNormalization.CM.equiv E B ⟨Source.UnitaryEq.CM.Frames.period E g z.val, Source.UnitaryEq.CM.PrescribedAction.period_preserves E g z.val z.property⟩ := by
  have hl := line_action E L g z
  have hm := hG.2.1 (ThetaArchimedeanAction.CM.rational E L g)
  change (RepresentationTheory.Theta.Adelic.BallNatural.asSL (T.ball (ThetaArchimedeanAction.CM.rational E L g))).val =
    RepresentationTheory.Theta.Adelic.BallGeometryData.standardMatrix (Source.BallArithmetic.CM.data E L)
      (ThetaArchimedeanAction.CM.rational E L g) places.distinguished at hm
  rw [← hm] at hl
  apply Subtype.ext
  exact chart_of_line _ _ _ (Source.PeriodDifferential.CM.lineScale E g z.val)
    (Source.PeriodDifferential.CM.lineScale_ne_zero E g z.val z.property) hl

include hG in
theorem factor (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : B.Domain) :
    RepresentationTheory.Theta.Adelic.BallNatural.Factors.automorphyFactor
      (T.ball (ThetaArchimedeanAction.CM.rational E L g)) (Source.BallNormalization.CM.equiv E B z) =
        Source.PeriodDifferential.CM.lineScale E g z.val := by
  have hl := line_action E L g z
  have hm := hG.2.1 (ThetaArchimedeanAction.CM.rational E L g)
  change (RepresentationTheory.Theta.Adelic.BallNatural.asSL (T.ball (ThetaArchimedeanAction.CM.rational E L g))).val =
    RepresentationTheory.Theta.Adelic.BallGeometryData.standardMatrix (Source.BallArithmetic.CM.data E L)
      (ThetaArchimedeanAction.CM.rational E L g) places.distinguished at hm
  rw [← hm] at hl
  have h := congrFun hl 2
  change RepresentationTheory.Theta.Adelic.BallNatural.Factors.automorphyFactor
    (T.ball (ThetaArchimedeanAction.CM.rational E L g)) (Source.BallNormalization.CM.equiv E B z) =
      Source.PeriodDifferential.CM.lineScale E g z.val * 1 at h
  exact h.trans (mul_one _)

include hG in
theorem natural_half (g : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU B.b) (z : B.Domain) :
    RepresentationTheory.Theta.Adelic.BallNatural.Factors.naturalHalfFactor 1
      (T.ball (ThetaArchimedeanAction.CM.rational E L g)) (Source.BallNormalization.CM.equiv E B z) =
        Source.PeriodDifferential.CM.lineScale E g z.val := by
  rw [RepresentationTheory.Theta.Adelic.BallNatural.Factors.naturalHalfFactor, pow_one, factor E L T hG]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaBallAction.CM
