import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.OpenRatioSections

/-! # Open Ratio Pullback -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.OpenRatioPullback

noncomputable section

/-! Restriction of the Segre open ratio sections to their canonical
affine charts agrees with the previously checked chart-coordinate formulas. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable (R : CommRingCat.{u}) {n m : ℕ} (p : AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} n m)

theorem segreRowRatioSection_pullback (a : Fin (n + 1)) :
    (AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left.appLE (OpenRatioSections.segreCoordinateOpen R p) ⊤
      (OpenRatioSections.segreChart_top_le_coordinateOpen R p) (OpenRatioSections.segreRowRatioSection R p a) =
      (Scheme.ΓSpecIso (CommRingCat.of (AbelianModuli.HilbertConstruction.Segre.ProjectiveCharts.SegreHomogeneousChart R p.1 p.2))).inv
        (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreChartCoordinate R p.1 p.2 (ULift.up a, p.2)) := by
  let s := Proj.awayToSection (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (X p.1.down)
    (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.1.down (X a))
  have he := congrArg (fun k : Γ(Proj (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n),
    Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (X p.1.down)) ⟶
      Γ((AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreHomogeneousChartScheme R p.1 p.2).left, ⊤) => k s)
    (Scheme.Hom.appLE_comp_appLE (AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left
      (AbelianModuli.HilbertConstruction.Segre.ProjectionGluing.segreRowProjection R n m) _ _ _ (OpenRatioSections.segreCoordinateOpen_le_row R p)
      (OpenRatioSections.segreChart_top_le_coordinateOpen R p))
  have hrow := RowColumnSections.segreRowChart_section R p a (ChartRatioIdentity.segreRowChart_top_le R p)
  have hp : (AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left.appLE (OpenRatioSections.segreCoordinateOpen R p) ⊤
      (OpenRatioSections.segreChart_top_le_coordinateOpen R p) (OpenRatioSections.segreRowRatioSection R p a) =
      (AbelianModuli.HilbertConstruction.Segre.ChartProjections.segreRowChartMap R p).appLE (Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (X p.1.down)) ⊤
        (ChartRatioIdentity.segreRowChart_top_le R p) s := by
    simpa only [AbelianModuli.HilbertConstruction.Segre.ProjectionGluing.segreRowProjection_chart] using! he
  exact hp.trans hrow

theorem segreColumnRatioSection_pullback (b : Fin (m + 1)) :
    (AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left.appLE (OpenRatioSections.segreCoordinateOpen R p) ⊤
      (OpenRatioSections.segreChart_top_le_coordinateOpen R p) (OpenRatioSections.segreColumnRatioSection R p b) =
      (Scheme.ΓSpecIso (CommRingCat.of (AbelianModuli.HilbertConstruction.Segre.ProjectiveCharts.SegreHomogeneousChart R p.1 p.2))).inv
        (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreChartCoordinate R p.1 p.2 (p.1, ULift.up b)) := by
  let s := Proj.awayToSection (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R m) (X p.2.down)
    (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.2.down (X b))
  have he := congrArg (fun k : Γ(Proj (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R m),
    Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R m) (X p.2.down)) ⟶
      Γ((AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreHomogeneousChartScheme R p.1 p.2).left, ⊤) => k s)
    (Scheme.Hom.appLE_comp_appLE (AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left
      (AbelianModuli.HilbertConstruction.Segre.ProjectionGluing.segreColumnProjection R n m) _ _ _ (OpenRatioSections.segreCoordinateOpen_le_column R p)
      (OpenRatioSections.segreChart_top_le_coordinateOpen R p))
  have hcol := RowColumnSections.segreColumnChart_section R p b (ChartRatioIdentity.segreColumnChart_top_le R p)
  have hp : (AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left.appLE (OpenRatioSections.segreCoordinateOpen R p) ⊤
      (OpenRatioSections.segreChart_top_le_coordinateOpen R p) (OpenRatioSections.segreColumnRatioSection R p b) =
      (AbelianModuli.HilbertConstruction.Segre.ChartProjections.segreColumnChartMap R p).appLE (Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R m) (X p.2.down)) ⊤
        (ChartRatioIdentity.segreColumnChart_top_le R p) s := by
    simpa only [AbelianModuli.HilbertConstruction.Segre.ProjectionGluing.segreColumnProjection_chart] using! he
  exact hp.trans hcol

theorem segreAmbientRatioSection_pullback (q : AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} n m) :
    (AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left.appLE (OpenRatioSections.segreCoordinateOpen R p) ⊤
      (OpenRatioSections.segreChart_top_le_coordinateOpen R p) (OpenRatioSections.segreAmbientRatioSection R p q) =
      (Scheme.ΓSpecIso (CommRingCat.of (AbelianModuli.HilbertConstruction.Segre.ProjectiveCharts.SegreHomogeneousChart R p.1 p.2))).inv
        (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreChartCoordinate R p.1 p.2 q) := by
  let s := Proj.awayToSection (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} n m) R) (X p)
    (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p (X q))
  have he := congrArg (fun k : Γ(Proj (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} n m) R),
    Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} n m) R) (X p)) ⟶
      Γ((AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreHomogeneousChartScheme R p.1 p.2).left, ⊤) => k s)
    (Scheme.Hom.appLE_comp_appLE (AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left
      (AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreProjectiveInclusion R) _ _ _ le_rfl (OpenRatioSections.segreChart_top_le_coordinateOpen R p))
  exact he.trans (TargetChartSections.segreTargetChart_section R p q (ChartRatioIdentity.segreTargetChart_top_le R p))

theorem segreOpen_ratio_identity (a : Fin (n + 1)) (b : Fin (m + 1)) :
    OpenRatioSections.segreAmbientRatioSection R p (ULift.up a, ULift.up b) =
      OpenRatioSections.segreRowRatioSection R p a * OpenRatioSections.segreColumnRatioSection R p b := by
  let j : Γ(AbelianModuli.HilbertConstruction.Segre.ProductComparison.segreEquationScheme R n m, OpenRatioSections.segreCoordinateOpen R p) ⟶
      Γ((AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreHomogeneousChartScheme R p.1 p.2).left, ⊤) :=
    (AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left.appLE (OpenRatioSections.segreCoordinateOpen R p) ⊤
      (OpenRatioSections.segreChart_top_le_coordinateOpen R p)
  let e := (Scheme.ΓSpecIso (CommRingCat.of (AbelianModuli.HilbertConstruction.Segre.ProjectiveCharts.SegreHomogeneousChart R p.1 p.2))).inv
  have hm : e (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreChartCoordinate R p.1 p.2 (ULift.up a, ULift.up b)) =
      e (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreChartCoordinate R p.1 p.2 (ULift.up a, p.2)) *
        e (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreChartCoordinate R p.1 p.2 (p.1, ULift.up b)) :=
    (congrArg e (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreChartCoordinate_entry R p.1 (ULift.up a) p.2 (ULift.up b))).trans
      (map_mul e.hom _ _)
  have hj : j (OpenRatioSections.segreAmbientRatioSection R p (ULift.up a, ULift.up b)) =
      j (OpenRatioSections.segreRowRatioSection R p a) * j (OpenRatioSections.segreColumnRatioSection R p b) :=
    (segreAmbientRatioSection_pullback R p (ULift.up a, ULift.up b)).trans
      (hm.trans (congrArg₂ (fun x y => x * y)
        (segreRowRatioSection_pullback R p a) (segreColumnRatioSection_pullback R p b)).symm)
  exact OpenRatioSections.segreChart_appLE_injective R p (hj.trans (map_mul j.hom _ _).symm)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.OpenRatioPullback
