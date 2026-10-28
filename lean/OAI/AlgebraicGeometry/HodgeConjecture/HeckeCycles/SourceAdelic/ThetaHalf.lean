import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaPeriodComparison
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaAdaptedCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Adelic.ThetaGeometricCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.MultiplierSign

/-! # Theta Half -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaHalf.CM.FrameComparison

/-! The actual AdelicTheta Hodge frame, the constant diagonal component change,
and the source graph frame multiply to the derived symplectic denominator. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalFrame.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaComplexFrame.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.UnitaryEq.CM.PeriodCovariance OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ComplexAction.CM
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) (T : ThetaRationalFrame.CM.Data E L)
  (hT : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification T (Source.GlobalFrames.CM.frames E
    (OppositeCoordinates.CM.coordinates E L.coordinates)))
  (hG : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification T)

include hG in
theorem value (z : B.Domain) (x : GeometricSource.CM.Positions E places → ℂ) :
    ((T.frame (Source.BallNormalization.CM.equiv E B z)).val.submatrix (ThetaRationalFrame.CM.index E L) (ThetaRationalFrame.CM.index E L)).mulVec
      ((ThetaAdaptedCoordinates.CM.diagonal E L).val.mulVec
        (Source.MultiplierSign.CM.Square.graphFrame E L z.val x)) =
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)).complexify.denominator (L.period z.val).matrix).mulVec x := by
  let w := GeometricSource.CM.graphInAmbient E L.coordinates (L.period z.val) x
  obtain ⟨t, ht⟩ := ThetaPeriodComparison.CM.native_graph E L T hT hG z x
  have hc :
      (T.frame (Source.BallNormalization.CM.equiv E B z)).val.mulVec
        (RepresentationTheory.Theta.Adelic.BallGeometryData.geometricCoordinates (Source.BallArithmetic.CM.data E L)
          (ThetaComplexComponents.CM.components E L w)) = t := by
    rw [← ThetaComplexFrame.CM.apply E L T hT w]
    change (T.frame _).val.mulVec (RepresentationTheory.Theta.Adelic.BallGeometryData.geometricCoordinates _ (T.complexPhase (ThetaComplexFrame.CM.nativeFrame E L T hT w))) = t
    rw [show ThetaComplexFrame.CM.nativeFrame E L T hT w = _ from ht]
    exact Adelic.ThetaGeometricCoordinates.CM.frame_coordinates T hG _ t
  have hs := ThetaPeriodComparison.CM.phase E L T hT w
  change Rational.FrameComplexChange.CM.swap (ThetaRationalFrame.CM.index E L)
    (ThetaComplexFrame.CM.nativeFrame E L T hT (GeometricSource.CM.graphInAmbient E L.coordinates (L.period z.val) x)) = _ at hs
  rw [ht, ComplexGraphReindex.CM.graph, Source.UnitaryEq.CM.PeriodCovariance.complexFrame_graph E L z.val x, Source.UnitaryEq.CM.PeriodCovariance.block_graph_action] at hs
  have hd : t ∘ ThetaRationalFrame.CM.index E L =
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)).complexify.denominator (L.period z.val).matrix).mulVec x :=
    congrArg (fun f : (GeometricSource.CM.Positions E places ⊕ GeometricSource.CM.Positions E places) → ℂ => fun i => f (.inr i)) hs
  have he := congrArg (fun f => f ∘ ThetaRationalFrame.CM.index E L) hc
  rw [← ComplexGraphReindex.CM.mulVec] at he
  have ha := ThetaAdaptedCoordinates.CM.coordinates E L w
  change (RepresentationTheory.Theta.Adelic.BallGeometryData.geometricCoordinates (Source.BallArithmetic.CM.data E L)
    (ThetaComplexComponents.CM.components E L w)) ∘ ThetaRationalFrame.CM.index E L = _ at ha
  rw [ha] at he
  exact he.trans hd

include hG in
theorem matrix_identity (z : B.Domain) :
    (T.frame (Source.BallNormalization.CM.equiv E B z)).val.submatrix (ThetaRationalFrame.CM.index E L) (ThetaRationalFrame.CM.index E L) *
      (ThetaAdaptedCoordinates.CM.diagonal E L).val *
        LinearMap.toMatrix' (Source.MultiplierSign.CM.Square.graphFrame E L z.val) =
      (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)).complexify.denominator (L.period z.val).matrix := by
  apply Matrix.mulVec_injective
  funext x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec]
  exact value E L T hT hG z x

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaHalf.CM.FrameComparison

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaHalf.CM.Determinant

/-! The two actual half-determinant frames have a ratio with a fixed,
nonzero square, determined by the constant adapted-coordinate matrix. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalFrame.CM
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) (T : ThetaRationalFrame.CM.Data E L)
  (hT : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification T (Source.GlobalFrames.CM.frames E
    (OppositeCoordinates.CM.coordinates E L.coordinates)))
  (hG : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification T)

include hG in
theorem determinant (z : B.Domain) :
    T.halfFrame (Source.BallNormalization.CM.equiv E B z) ^ 2 *
      (ThetaAdaptedCoordinates.CM.diagonal E L).val.det * (L.halfDet z.val : ℂ) ^ 2 =
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)).complexify.denominator (L.period z.val).matrix).det := by
  have h := congrArg Matrix.det (FrameComparison.matrix_identity E L T hT hG z)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_submatrix_equiv_self, LinearMap.det_toMatrix'] at h
  rw [(hG.2.2.2.2.2.1 (Source.BallNormalization.CM.equiv E B z)).2, L.halfDet_square z.val z.property]
  exact h

def ratio (z : B.Domain) : ℂ :=
  T.halfFrame (Source.BallNormalization.CM.equiv E B z) * (L.halfDet z.val : ℂ) /
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)) (L.period z.val)

include hG in
theorem ratio_ne_zero (z : B.Domain) : ratio E L T hT z ≠ 0 :=
  div_ne_zero (mul_ne_zero (hG.2.2.2.2.2.1 (Source.BallNormalization.CM.equiv E B z)).1 (Units.ne_zero _))
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet_ne_zero _ _)

include hG in
theorem ratio_square (z : B.Domain) :
    ratio E L T hT z ^ 2 = ((ThetaAdaptedCoordinates.CM.diagonal E L).val.det)⁻¹ := by
  have hk : (ThetaAdaptedCoordinates.CM.diagonal E L).val.det ≠ 0 :=
    (Matrix.isUnits_det_units (ThetaAdaptedCoordinates.CM.diagonal E L)).ne_zero
  have hd := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)).denominator_det_isUnit (L.period z.val)
  rw [ratio, div_pow, mul_pow, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet_sq]
  apply (div_eq_iff hd.ne_zero).mpr
  rw [← determinant E L T hT hG z]
  field_simp

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaHalf.CM.Determinant

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaHalf.CM.DeterminantConstant

/-! Connectedness of the actual source ball makes the half-determinant
comparison a single nonzero constant, independent of the period point. -/

open scoped Classical _root_.NumberField
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalFrame.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaHalf.CM.Determinant
open OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d) (T : ThetaRationalFrame.CM.Data E L)
  (hT : RepresentationTheory.Theta.Adelic.DataTheta.CoordinateIdentification T (Source.GlobalFrames.CM.frames E
    (OppositeCoordinates.CM.coordinates E L.coordinates)))
  (hG : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification T)

include hG in
theorem native_continuous : Continuous (fun z : B.Domain =>
    T.halfFrame (Source.BallNormalization.CM.equiv E B z)) := by
  have hh : Continuous T.halfFrame := by
    have h := hG.2.2.2.2.1.continuousOn
    rw [continuousOn_iff_continuous_domRestrict] at h
    apply h.congr
    intro z
    exact dite_eq_left z.property
  exact hh.comp (Source.BallNormalization.CM.homeomorph E B).continuous

omit [IsGalois ℚ E] in
theorem source_continuous : Continuous (fun z : B.Domain => (L.halfDet z.val : ℂ)) := by
  have h := L.halfDet_holomorphic.continuousOn
  rw [continuousOn_iff_continuous_domRestrict] at h
  exact h

theorem symplectic_continuous : Continuous (fun z : B.Domain =>
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)) (L.period z.val)) := by
  have h := (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDetExtension_continuousOn (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT))).comp
    L.holomorphic.continuousOn (fun z _ =>
      (show (L.period z).matrix ∈ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.siegelSet (GeometricSource.CM.Positions E places) from
        ⟨(L.period z).symmetric, (L.period z).imaginary_posDef⟩))
  rw [continuousOn_iff_continuous_domRestrict] at h
  apply h.congr
  intro z
  simp only [Set.domRestrict_def, Function.comp_apply, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDetExtension, dite_eq_left
    (show (L.period z.val).matrix ∈ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.siegelSet (GeometricSource.CM.Positions E places) from
      ⟨(L.period z.val).symmetric, (L.period z.val).imaginary_posDef⟩)]
  rfl

include hG in
theorem ratio_continuous : Continuous (Determinant.ratio E L T hT) :=
  ((native_continuous E L T hG).mul (source_continuous E L)).div
    (symplectic_continuous E L T hT) (fun _ => RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet_ne_zero _ _)

def scalar : ℂ := Determinant.ratio E L T hT ⟨0, Source.MultiplierSign.CM.zero_mem_domain E⟩

include hG in
theorem scalar_ne_zero : scalar E L T hT ≠ 0 := Determinant.ratio_ne_zero E L T hT hG _

include hG in
theorem constant (z : B.Domain) : Determinant.ratio E L T hT z = scalar E L T hT := by
  let : PreconnectedSpace B.Domain := isPreconnected_iff_preconnectedSpace.mp
    (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ball_pathConnected (B.b : ℂ) B.negative).isConnected.isPreconnected
  let z0 : B.Domain := ⟨0, Source.MultiplierSign.CM.zero_mem_domain E⟩
  have hsq : Set.EqOn (Determinant.ratio E L T hT ^ 2) ((fun _ : B.Domain => Determinant.ratio E L T hT z0) ^ 2) Set.univ := by
    intro x _
    exact (Determinant.ratio_square E L T hT hG x).trans (Determinant.ratio_square E L T hT hG z0).symm
  have he := isPreconnected_univ.eq_of_sq_eq (ratio_continuous E L T hT hG).continuousOn
    (continuousOn_const (c := Determinant.ratio E L T hT z0)) hsq
    (fun _ => Determinant.ratio_ne_zero E L T hT hG z0) (Set.mem_univ z0) rfl
  exact he (Set.mem_univ z)

include hG in
theorem halfFrame_identity (z : B.Domain) :
    T.halfFrame (Source.BallNormalization.CM.equiv E B z) * (L.halfDet z.val : ℂ) =
      scalar E L T hT * RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)) (L.period z.val) :=
  (div_eq_iff (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.halfDet_ne_zero _ _)).mp (constant E L T hT hG z)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaHalf.CM.DeterminantConstant

end

end OAI
