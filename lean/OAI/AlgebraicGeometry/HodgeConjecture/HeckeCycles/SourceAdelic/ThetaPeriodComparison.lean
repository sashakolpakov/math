import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaComparison
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComplexGraphReindex
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PeriodFromGraph

/-! # Theta Period Comparison -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaPeriodComparison.CM

noncomputable section

/-! AdelicTheta's actual period, relabeled in the source index, is exactly the
symplectic transform of the original source period by the derived rational
matrix. This follows from the proved Hodge-subspace identification. -/

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

theorem phase (w : GeometricSource.CM.Ambient E) :
    Rational.FrameComplexChange.CM.swap (ThetaRationalFrame.CM.index E L) (ThetaComplexFrame.CM.nativeFrame E L T hT w) =
      (ThetaRationalFrame.CM.matrix E L T hT).val.map (algebraMap ℚ ℂ) *ᵥ Source.ComplexAction.CM.complexFrame E L.coordinates w := by
  change Rational.FrameComplexChange.CM.swap (ThetaRationalFrame.CM.index E L)
    ((Rational.FrameComplexChange.CM.swap (ThetaRationalFrame.CM.index E L)).symm _) = _
  exact (Rational.FrameComplexChange.CM.swap (ThetaRationalFrame.CM.index E L)).apply_symm_apply _

variable (hG : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification T)

include hG in
theorem native_graph (z : B.Domain) (x : GeometricSource.CM.Positions E places → ℂ) :
    ∃ t : RepresentationTheory.Theta.Adelic.BallGeometryData.FrameIndex (Source.BallArithmetic.CM.data E L) → ℂ,
      ThetaComplexFrame.CM.nativeFrame E L T hT (GeometricSource.CM.graphInAmbient E L.coordinates (L.period z.val) x) =
        Sum.elim t ((T.period (Source.BallNormalization.CM.equiv E B z)).matrix.mulVec t) := by
  have hp := Source.UnitaryEq.CM.PeriodCovariance.graph_prescribed E L z.val z.property x
  have hm := (ThetaComparison.CM.equiv_mem E L T hT z
    (GeometricSource.CM.graphInAmbient E L.coordinates (L.period z.val) x)).mpr hp
  obtain ⟨t, ht⟩ := (hG.2.2.2.2.2.2.2.1 (Source.BallNormalization.CM.equiv E B z)
    (ThetaComplexFrame.CM.equiv E L T hT
      (GeometricSource.CM.graphInAmbient E L.coordinates (L.period z.val) x))).mp hm
  refine ⟨t, ?_⟩
  apply T.complexPhase.injective
  exact ht.symm

include hG in
theorem transformed_graph (z : B.Domain) (x : GeometricSource.CM.Positions E places → ℂ) :
    ∃ y : GeometricSource.CM.Positions E places → ℂ,
      (ThetaRationalFrame.CM.matrix E L T hT).val.map (algebraMap ℚ ℂ) *ᵥ Source.UnitaryEq.CM.PeriodCovariance.graphPhase (L.period z.val) x =
        Sum.elim
          (((T.period (Source.BallNormalization.CM.equiv E B z)).matrix.submatrix
            (ThetaRationalFrame.CM.index E L) (ThetaRationalFrame.CM.index E L)).mulVec y) y := by
  obtain ⟨t, ht⟩ := native_graph E L T hT hG z x
  refine ⟨t ∘ ThetaRationalFrame.CM.index E L, ?_⟩
  rw [← Source.UnitaryEq.CM.PeriodCovariance.complexFrame_graph E L z.val x, ← phase E L T hT, ht, ComplexGraphReindex.CM.graph]

include hG in
theorem period_matrix (z : B.Domain) :
    (T.period (Source.BallNormalization.CM.equiv E B z)).matrix.submatrix (ThetaRationalFrame.CM.index E L) (ThetaRationalFrame.CM.index E L) =
      ((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.realBlocks (ThetaRationalFrame.CM.matrix E L T hT)).transformSiegel (L.period z.val)).matrix :=
  PeriodFromGraph.CM.matrix_eq (ThetaRationalFrame.CM.matrix E L T hT) (L.period z.val) _
    (transformed_graph E L T hT hG z)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaPeriodComparison.CM
