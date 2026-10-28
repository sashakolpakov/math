import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ChartCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.ChartMaps

/-! # Overlap Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.OverlapCoordinates

noncomputable section

/-! Coordinate restrictions to intersections of two Segre projective charts. -/

open _root_.MvPolynomial _root_.HomogeneousLocalization
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.ChartMaps

universe u v w

variable (R : Type u) [CommRing R] {σ : Type v} {τ : Type w} (p q : σ × τ)

abbrev SegreDoubleChart := Away (ChartCoordinates.segreQuotientGrading R)
  ((ChartCoordinates.segreVariable R p).val * (ChartCoordinates.segreVariable R q).val)

def segreOverlapLeft : ProjectiveCharts.SegreHomogeneousChart R p.1 p.2 →ₐ[R] SegreDoubleChart R p q :=
  HilbertScheme.Presentations.Homogeneous.ChartMaps.homogeneousOverlapLeft _ (ChartCoordinates.segreVariable R q).property

def segreOverlapRight : ProjectiveCharts.SegreHomogeneousChart R q.1 q.2 →ₐ[R] SegreDoubleChart R p q :=
  HilbertScheme.Presentations.Homogeneous.ChartMaps.homogeneousOverlapRight _ (ChartCoordinates.segreVariable R p).property

def segreOverlapCoordinateLeft (k : σ × τ) : SegreDoubleChart R p q :=
  segreOverlapLeft R p q (ChartCoordinates.segreChartCoordinate R p.1 p.2 k)

def segreOverlapCoordinateRight (k : σ × τ) : SegreDoubleChart R p q :=
  segreOverlapRight R p q (ChartCoordinates.segreChartCoordinate R q.1 q.2 k)

theorem segreOverlapCoordinateLeft_ratio (k : σ × τ) :
    segreOverlapCoordinateLeft R p q k = HilbertScheme.Presentations.Homogeneous.ChartRatios.overlapRatioLeft (ChartCoordinates.segreQuotientGrading R)
      (ChartCoordinates.segreVariable R p).property (ChartCoordinates.segreVariable R q).property (ChartCoordinates.segreVariable R k) := by
  unfold segreOverlapCoordinateLeft ChartCoordinates.segreChartCoordinate
  rw [HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective.affineChartMap_homogeneous _ _ (isHomogeneous_X R k)]
  exact HilbertScheme.Presentations.Homogeneous.ChartMaps.homogeneousOverlapLeft_ratio (ChartCoordinates.segreQuotientGrading R)
    (ChartCoordinates.segreVariable R p).property (ChartCoordinates.segreVariable R q).property (ChartCoordinates.segreVariable R k)

theorem segreOverlapCoordinateRight_ratio (k : σ × τ) :
    segreOverlapCoordinateRight R p q k = HilbertScheme.Presentations.Homogeneous.ChartRatios.overlapRatioRight (ChartCoordinates.segreQuotientGrading R)
      (ChartCoordinates.segreVariable R p).property (ChartCoordinates.segreVariable R q).property (ChartCoordinates.segreVariable R k) := by
  unfold segreOverlapCoordinateRight ChartCoordinates.segreChartCoordinate
  rw [HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective.affineChartMap_homogeneous _ _ (isHomogeneous_X R k)]
  exact HilbertScheme.Presentations.Homogeneous.ChartMaps.homogeneousOverlapRight_ratio (ChartCoordinates.segreQuotientGrading R)
    (ChartCoordinates.segreVariable R p).property (ChartCoordinates.segreVariable R q).property (ChartCoordinates.segreVariable R k)

theorem segreOverlapCoordinateLeft_pivot : segreOverlapCoordinateLeft R p q p = 1 := by
  rw [segreOverlapCoordinateLeft, ChartCoordinates.segreChartCoordinate_pivot, map_one]

theorem segreOverlapCoordinateRight_pivot : segreOverlapCoordinateRight R p q q = 1 := by
  rw [segreOverlapCoordinateRight, ChartCoordinates.segreChartCoordinate_pivot, map_one]

theorem segreOverlapCoordinateLeft_entry (a : σ) (b : τ) :
    segreOverlapCoordinateLeft R p q (a, b) =
      segreOverlapCoordinateLeft R p q (a, p.2) * segreOverlapCoordinateLeft R p q (p.1, b) := by
  exact (congrArg (segreOverlapLeft R p q) (ChartCoordinates.segreChartCoordinate_entry R p.1 a p.2 b)).trans
    ((segreOverlapLeft R p q).map_mul _ _)

theorem segreOverlapCoordinate_pivot_isUnit : IsUnit (segreOverlapCoordinateLeft R p q q) := by
  rw [segreOverlapCoordinateLeft_ratio]
  exact HilbertScheme.Presentations.Homogeneous.ChartRatios.overlapRatio_pivot_isUnit (ChartCoordinates.segreQuotientGrading R)
    (ChartCoordinates.segreVariable R p).property (ChartCoordinates.segreVariable R q).property

theorem segreOverlapCoordinate_cross (k : σ × τ) :
    segreOverlapCoordinateLeft R p q q * segreOverlapCoordinateRight R p q k =
      segreOverlapCoordinateLeft R p q k := by
  rw [segreOverlapCoordinateLeft_ratio, segreOverlapCoordinateRight_ratio,
    segreOverlapCoordinateLeft_ratio]
  exact HilbertScheme.Presentations.Homogeneous.ChartRatios.overlapRatio_cross (ChartCoordinates.segreQuotientGrading R)
    (ChartCoordinates.segreVariable R p).property (ChartCoordinates.segreVariable R q).property (ChartCoordinates.segreVariable R k)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.OverlapCoordinates
