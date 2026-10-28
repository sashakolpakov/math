import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaCompactComponents
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaRationalFrame

/-! # Theta Adapted Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaAdaptedCoordinates.CM

noncomputable section

/-! The source adapted frame and AdelicTheta's geometric frame differ by an
explicit constant invertible diagonal matrix, derived from the actual
archimedean tensor bases. -/

open scoped Classical _root_.NumberField _root_.Matrix
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaComplexComponents.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaCompactComponents.CM.ComponentValues
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {B : GeometricSource.CM.BallDatum E} {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
  (L : GeometricSource.CM.LinePeriod E B places d)

def factor (p : GeometricSource.CM.Positions E places) : ℂ :=
  if p.1 = places.distinguished then
    if p.2 = 0 then ThetaCompactComponents.CM.ComponentValues.coefficient E L p.1 (2, 0)
    else ThetaComplexComponents.CM.sign E L p.1 (p.2 - 1, 0) * ThetaCompactComponents.CM.ComponentValues.coefficient E L p.1 (p.2 - 1, 0)
  else if d (places.representative p.1) then
    ThetaComplexComponents.CM.sign E L p.1 (p.2, 0) * ThetaCompactComponents.CM.ComponentValues.coefficient E L p.1 (p.2, 0)
  else ThetaCompactComponents.CM.ComponentValues.coefficient E L p.1 (p.2, 0)

theorem factor_ne_zero (p : GeometricSource.CM.Positions E places) : factor E L p ≠ 0 := by
  unfold factor
  split_ifs
  · exact ThetaCompactComponents.CM.ComponentValues.coefficient_ne_zero E L p.1 (2, 0)
  · exact mul_ne_zero (ThetaCompactComponents.CM.sign_ne_zero E L p.1 (p.2 - 1, 0))
      (ThetaCompactComponents.CM.ComponentValues.coefficient_ne_zero E L p.1 (p.2 - 1, 0))
  · exact mul_ne_zero (ThetaCompactComponents.CM.sign_ne_zero E L p.1 (p.2, 0))
      (ThetaCompactComponents.CM.ComponentValues.coefficient_ne_zero E L p.1 (p.2, 0))
  · exact ThetaCompactComponents.CM.ComponentValues.coefficient_ne_zero E L p.1 (p.2, 0)

def diagonal : (Matrix (GeometricSource.CM.Positions E places) (GeometricSource.CM.Positions E places) ℂ)ˣ :=
  Source.QuadraticForms.CM.diagonalUnit (fun p => Units.mk0 (factor E L p) (factor_ne_zero E L p))

theorem diagonal_val : (CM.diagonal E L).val = Matrix.diagonal (factor E L) := rfl

theorem index_value (p : GeometricSource.CM.Positions E places) :
    ThetaRationalFrame.CM.index E L p = (p.1, p.2, 0) := rfl

theorem value (w : GeometricSource.CM.Ambient E) (p : GeometricSource.CM.Positions E places) :
    RepresentationTheory.Theta.Adelic.BallGeometryData.geometricCoordinates (Source.BallArithmetic.CM.data E L) (ThetaComplexComponents.CM.components E L w)
      (ThetaRationalFrame.CM.index E L p) =
        factor E L p * GeometricSource.CM.adaptedCoordinates E places d w p := by
  rcases p with ⟨v, i⟩
  rw [index_value]
  by_cases hv : v = places.distinguished
  · subst v
    fin_cases i
    · simpa [RepresentationTheory.Theta.Adelic.BallGeometryData.geometricCoordinates, factor, GeometricSource.CM.adaptedCoordinates,
        Source.BallArithmetic.CM.data] using ThetaCompactComponents.CM.ComponentValues.standard E L w places.distinguished (2, 0)
    · simpa [RepresentationTheory.Theta.Adelic.BallGeometryData.geometricCoordinates, factor, GeometricSource.CM.adaptedCoordinates,
        Source.BallArithmetic.CM.data] using ThetaCompactComponents.CM.ComponentValues.dual E L w places.distinguished (0, 0)
    · simpa [RepresentationTheory.Theta.Adelic.BallGeometryData.geometricCoordinates, factor, GeometricSource.CM.adaptedCoordinates,
        Source.BallArithmetic.CM.data] using ThetaCompactComponents.CM.ComponentValues.dual E L w places.distinguished (1, 0)
  · have hp : (Source.BallArithmetic.CM.data E L).positive v 0 = !(d (places.representative v)) := by
      change (if v = places.distinguished then false else !(d (places.representative v))) = _
      rw [ite_eq_right hv]
    change (if v = places.distinguished then _ else
      if (Source.BallArithmetic.CM.data E L).positive v 0 then (ThetaComplexComponents.CM.components E L w v).1 (i, 0)
        else (ThetaComplexComponents.CM.components E L w v).2 (i, 0)) = _
    rw [ite_eq_right hv, hp]
    cases hd : d (places.representative v)
    · simpa only [Bool.not_false, ite_true, factor, ite_eq_right hv, hd, Bool.false_eq_true, ite_false,
        GeometricSource.CM.adaptedCoordinates, LinearMap.coe_mk, AddHom.coe_mk] using ThetaCompactComponents.CM.ComponentValues.standard E L w v (i, 0)
    · simpa only [Bool.not_true, Bool.false_eq_true, ite_false, factor, ite_eq_right hv, hd, ite_true,
        GeometricSource.CM.adaptedCoordinates, LinearMap.coe_mk, AddHom.coe_mk] using ThetaCompactComponents.CM.ComponentValues.dual E L w v (i, 0)

theorem coordinates (w : GeometricSource.CM.Ambient E) :
    (fun p => RepresentationTheory.Theta.Adelic.BallGeometryData.geometricCoordinates (Source.BallArithmetic.CM.data E L) (ThetaComplexComponents.CM.components E L w)
      (ThetaRationalFrame.CM.index E L p)) =
        (CM.diagonal E L).val.mulVec (GeometricSource.CM.adaptedCoordinates E places d w) := by
  rw [diagonal_val]
  funext p
  rw [Matrix.mulVec_diagonal]
  exact value E L w p

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SourceAdelic.ThetaAdaptedCoordinates.CM
