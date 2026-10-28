import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.CoordinateMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.RowColumnTransitions
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme

/-! # Chart Projections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ChartProjections

noncomputable section

/-! Row and column maps from Segre charts, compatible on their actual affine intersections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : CommRingCat.{u}) {n m : ℕ}

abbrev SegreProjectiveIndex (n m : ℕ) := ULift.{u} (Fin (n + 1)) × ULift.{u} (Fin (m + 1))

def segreRowChartMap (p : SegreProjectiveIndex.{u} n m) :
    (ProjectiveScheme.segreHomogeneousChartScheme R p.1 p.2).left ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace R n).left :=
  AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap R (ProjectiveCharts.SegreHomogeneousChart R p.1 p.2)
    (fun a => ChartCoordinates.segreChartCoordinate R p.1 p.2 (ULift.up a, p.2)) p.1.down
      (ChartCoordinates.segreChartCoordinate_pivot R p.1 p.2)

def segreColumnChartMap (p : SegreProjectiveIndex.{u} n m) :
    (ProjectiveScheme.segreHomogeneousChartScheme R p.1 p.2).left ⟶ (Projective.ProjectivePresentations.affineProjectiveSpace R m).left :=
  AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap R (ProjectiveCharts.SegreHomogeneousChart R p.1 p.2)
    (fun b => ChartCoordinates.segreChartCoordinate R p.1 p.2 (p.1, ULift.up b)) p.2.down
      (ChartCoordinates.segreChartCoordinate_pivot R p.1 p.2)

theorem segreRowChartMap_overlap (p q : SegreProjectiveIndex.{u} n m) :
    Spec.map (CommRingCat.ofHom (OverlapCoordinates.segreOverlapLeft R p q).toRingHom) ≫ segreRowChartMap R p =
      Spec.map (CommRingCat.ofHom (OverlapCoordinates.segreOverlapRight R p q).toRingHom) ≫ segreRowChartMap R q := by
  have hl := AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap_natural R (ProjectiveCharts.SegreHomogeneousChart R p.1 p.2)
    (OverlapCoordinates.segreOverlapLeft R p q) (fun a => ChartCoordinates.segreChartCoordinate R p.1 p.2 (ULift.up a, p.2)) p.1.down
    (ChartCoordinates.segreChartCoordinate_pivot R p.1 p.2)
  have hr := AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap_natural R (ProjectiveCharts.SegreHomogeneousChart R q.1 q.2)
    (OverlapCoordinates.segreOverlapRight R p q) (fun a => ChartCoordinates.segreChartCoordinate R q.1 q.2 (ULift.up a, q.2)) q.1.down
    (ChartCoordinates.segreChartCoordinate_pivot R q.1 q.2)
  exact hl.trans ((AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap_eq_of_cross R (OverlapCoordinates.SegreDoubleChart R p q)
    (fun a => OverlapCoordinates.segreOverlapCoordinateLeft R p q (ULift.up a, p.2))
    (fun a => OverlapCoordinates.segreOverlapCoordinateRight R p q (ULift.up a, q.2)) p.1.down q.1.down
    (OverlapCoordinates.segreOverlapCoordinateLeft_pivot R p q) (OverlapCoordinates.segreOverlapCoordinateRight_pivot R p q)
    (RowColumnTransitions.segreOverlap_rowPivot_isUnit R p q) (fun a => RowColumnTransitions.segreOverlap_rowCross R p q (ULift.up a))).trans hr.symm)

theorem segreColumnChartMap_overlap (p q : SegreProjectiveIndex.{u} n m) :
    Spec.map (CommRingCat.ofHom (OverlapCoordinates.segreOverlapLeft R p q).toRingHom) ≫ segreColumnChartMap R p =
      Spec.map (CommRingCat.ofHom (OverlapCoordinates.segreOverlapRight R p q).toRingHom) ≫ segreColumnChartMap R q := by
  have hl := AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap_natural R (ProjectiveCharts.SegreHomogeneousChart R p.1 p.2)
    (OverlapCoordinates.segreOverlapLeft R p q) (fun b => ChartCoordinates.segreChartCoordinate R p.1 p.2 (p.1, ULift.up b)) p.2.down
    (ChartCoordinates.segreChartCoordinate_pivot R p.1 p.2)
  have hr := AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap_natural R (ProjectiveCharts.SegreHomogeneousChart R q.1 q.2)
    (OverlapCoordinates.segreOverlapRight R p q) (fun b => ChartCoordinates.segreChartCoordinate R q.1 q.2 (q.1, ULift.up b)) q.2.down
    (ChartCoordinates.segreChartCoordinate_pivot R q.1 q.2)
  exact hl.trans ((AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap_eq_of_cross R (OverlapCoordinates.SegreDoubleChart R p q)
    (fun b => OverlapCoordinates.segreOverlapCoordinateLeft R p q (p.1, ULift.up b))
    (fun b => OverlapCoordinates.segreOverlapCoordinateRight R p q (q.1, ULift.up b)) p.2.down q.2.down
    (OverlapCoordinates.segreOverlapCoordinateLeft_pivot R p q) (OverlapCoordinates.segreOverlapCoordinateRight_pivot R p q)
    (RowColumnTransitions.segreOverlap_columnPivot_isUnit R p q) (fun b => RowColumnTransitions.segreOverlap_columnCross R p q (ULift.up b))).trans hr.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ChartProjections
