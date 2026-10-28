import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ProjectiveChartSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ChartProductAlgebra

/-! # Row Column Sections -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.RowColumnSections

noncomputable section

/-! The row and column projective ratios on a Segre chart are the
actual normalized row and column entries of its coordinate ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ChartProductAlgebra

universe u
variable (R : CommRingCat.{u}) {n m : ℕ} (p : AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} n m)

theorem segreRowChart_section (a : Fin (n + 1))
    (h : ⊤ ≤ AbelianModuli.HilbertConstruction.Segre.ChartProjections.segreRowChartMap R p ⁻¹ᵁ Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (X p.1.down)) :
    (AbelianModuli.HilbertConstruction.Segre.ChartProjections.segreRowChartMap R p).appLE (Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (X p.1.down)) ⊤ h
      (Proj.awayToSection (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (X p.1.down)
        (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.1.down (X a))) =
      (Scheme.ΓSpecIso (CommRingCat.of (AbelianModuli.HilbertConstruction.Segre.ProjectiveCharts.SegreHomogeneousChart R p.1 p.2))).inv
        (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreChartCoordinate R p.1 p.2 (ULift.up a, p.2)) := by
  let φ := (AbelianModuli.HilbertConstruction.Segre.ChartProductAlgebra.segreRowChartAlgebra R p).toRingHom
  have he := Affine.ProjectiveChartSections.affineProjectiveChart_pullback_section (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n)
    (isHomogeneous_X R p.1.down) Nat.zero_lt_one φ h
  have hv := congrArg (fun k : CommRingCat.of (AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing R n p.1.down) ⟶
    Γ(Spec (CommRingCat.of (AbelianModuli.HilbertConstruction.Segre.ProjectiveCharts.SegreHomogeneousChart R p.1 p.2)), ⊤) =>
      k (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.1.down (X a))) he
  change _ = (Scheme.ΓSpecIso (CommRingCat.of (AbelianModuli.HilbertConstruction.Segre.ProjectiveCharts.SegreHomogeneousChart R p.1 p.2))).inv (φ (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.1.down (X a))) at hv
  exact hv.trans (congrArg (Scheme.ΓSpecIso (CommRingCat.of (AbelianModuli.HilbertConstruction.Segre.ProjectiveCharts.SegreHomogeneousChart R p.1 p.2))).inv (AbelianModuli.HilbertConstruction.Segre.ChartProductAlgebra.segreRowChartAlgebra_coordinate R p a))

theorem segreColumnChart_section (b : Fin (m + 1))
    (h : ⊤ ≤ AbelianModuli.HilbertConstruction.Segre.ChartProjections.segreColumnChartMap R p ⁻¹ᵁ Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R m) (X p.2.down)) :
    (AbelianModuli.HilbertConstruction.Segre.ChartProjections.segreColumnChartMap R p).appLE (Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R m) (X p.2.down)) ⊤ h
      (Proj.awayToSection (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R m) (X p.2.down)
        (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.2.down (X b))) =
      (Scheme.ΓSpecIso (CommRingCat.of (AbelianModuli.HilbertConstruction.Segre.ProjectiveCharts.SegreHomogeneousChart R p.1 p.2))).inv
        (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreChartCoordinate R p.1 p.2 (p.1, ULift.up b)) := by
  let φ := (AbelianModuli.HilbertConstruction.Segre.ChartProductAlgebra.segreColumnChartAlgebra R p).toRingHom
  have he := Affine.ProjectiveChartSections.affineProjectiveChart_pullback_section (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R m)
    (isHomogeneous_X R p.2.down) Nat.zero_lt_one φ h
  have hv := congrArg (fun k : CommRingCat.of (AbelianModuli.HilbertConstruction.ProjectiveChart.Evaluation.projectiveChartRing R m p.2.down) ⟶
    Γ(Spec (CommRingCat.of (AbelianModuli.HilbertConstruction.Segre.ProjectiveCharts.SegreHomogeneousChart R p.1 p.2)), ⊤) =>
      k (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.2.down (X b))) he
  change _ = (Scheme.ΓSpecIso (CommRingCat.of (AbelianModuli.HilbertConstruction.Segre.ProjectiveCharts.SegreHomogeneousChart R p.1 p.2))).inv (φ (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.2.down (X b))) at hv
  exact hv.trans (congrArg (Scheme.ΓSpecIso (CommRingCat.of (AbelianModuli.HilbertConstruction.Segre.ProjectiveCharts.SegreHomogeneousChart R p.1 p.2))).inv (AbelianModuli.HilbertConstruction.Segre.ChartProductAlgebra.segreColumnChartAlgebra_coordinate R p b))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.RowColumnSections
