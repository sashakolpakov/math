import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.RowColumnSections
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.TargetChartSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.CoordinatePreimages

/-! # Chart Ratio Identity -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.ChartRatioIdentity

noncomputable section

/-! On every actual Segre affine chart, the ambient projective ratio
is exactly the product of the row and column ratios as regular sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AffineProjective.CoordinatePreimages

universe u
variable (R : CommRingCat.{u}) {n m : ℕ} (p : AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} n m)

theorem segreRowChart_top_le :
    ⊤ ≤ AbelianModuli.HilbertConstruction.Segre.ChartProjections.segreRowChartMap R p ⁻¹ᵁ Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (X p.1.down) := by
  have h := AbelianModuli.HilbertConstruction.AffineProjective.CoordinatePreimages.affineProjectiveCoordinateMap_preimage R (AbelianModuli.HilbertConstruction.Segre.ProjectiveCharts.SegreHomogeneousChart R p.1 p.2)
    (fun a => AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreChartCoordinate R p.1 p.2 (ULift.up a, p.2)) p.1.down
    (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreChartCoordinate_pivot R p.1 p.2) p.1.down
  rw [AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreChartCoordinate_pivot, PrimeSpectrum.basicOpen_one] at h
  exact h.ge

theorem segreColumnChart_top_le :
    ⊤ ≤ AbelianModuli.HilbertConstruction.Segre.ChartProjections.segreColumnChartMap R p ⁻¹ᵁ Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R m) (X p.2.down) := by
  have h := AbelianModuli.HilbertConstruction.AffineProjective.CoordinatePreimages.affineProjectiveCoordinateMap_preimage R (AbelianModuli.HilbertConstruction.Segre.ProjectiveCharts.SegreHomogeneousChart R p.1 p.2)
    (fun b => AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreChartCoordinate R p.1 p.2 (p.1, ULift.up b)) p.2.down
    (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreChartCoordinate_pivot R p.1 p.2) p.2.down
  rw [AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreChartCoordinate_pivot, PrimeSpectrum.basicOpen_one] at h
  exact h.ge

theorem segreTargetChart_top_le :
    ⊤ ≤ ((AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left ≫ AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreProjectiveInclusion R) ⁻¹ᵁ
      Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} n m) R) (X p) := by
  let I := AbelianModuli.HilbertConstruction.Segre.HomogeneousRelations.segreHomogeneousIdeal (σ := ULift.{u} (Fin (n + 1)))
    (τ := ULift.{u} (Fin (m + 1))) R
  change ⊤ ≤ (Proj.awayι (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I) (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I (X p))
    ((Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I).map_mem (isHomogeneous_X R p)) Nat.zero_lt_one) ⁻¹ᵁ
      (Proj.map (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I) (Homogeneous.Quotient.HomogeneousQuotient.irrelevant_quotient_le_map I) ⁻¹ᵁ
        Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} n m) R) (X p))
  rw [Proj.map_preimage_basicOpen, ← Proj.opensRange_awayι (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I)
    (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I (X p)) ((Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I).map_mem (isHomogeneous_X R p)) Nat.zero_lt_one,
    Scheme.Hom.preimage_opensRange]

theorem segreChart_ratio_identity (a : Fin (n + 1)) (b : Fin (m + 1)) :
    ((AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreHomogeneousChartMap R p.1 p.2).left ≫ AbelianModuli.HilbertConstruction.Segre.ProjectiveScheme.segreProjectiveInclusion R).appLE
      (Proj.basicOpen (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} n m) R) (X p)) ⊤
      (segreTargetChart_top_le R p)
      (Proj.awayToSection (Polynomial.Dehomogenization.PolynomialProjective.polynomialGrading (AbelianModuli.HilbertConstruction.Segre.ChartProjections.SegreProjectiveIndex.{u} n m) R) (X p)
        (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p (X (ULift.up a, ULift.up b)))) =
      (AbelianModuli.HilbertConstruction.Segre.ChartProjections.segreRowChartMap R p).appLE (Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (X p.1.down)) ⊤
        (segreRowChart_top_le R p)
        (Proj.awayToSection (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R n) (X p.1.down) (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.1.down (X a))) *
      (AbelianModuli.HilbertConstruction.Segre.ChartProjections.segreColumnChartMap R p).appLE (Proj.basicOpen (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R m) (X p.2.down)) ⊤
        (segreColumnChart_top_le R p)
        (Proj.awayToSection (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.coordinateGrading R m) (X p.2.down) (Polynomial.Dehomogenization.PolynomialProjective.dehomogenize p.2.down (X b))) := by
  have ht := TargetChartSections.segreTargetChart_section R p (ULift.up a, ULift.up b) (segreTargetChart_top_le R p)
  have hr := RowColumnSections.segreRowChart_section R p a (segreRowChart_top_le R p)
  have hc := RowColumnSections.segreColumnChart_section R p b (segreColumnChart_top_le R p)
  let e := (Scheme.ΓSpecIso (CommRingCat.of (AbelianModuli.HilbertConstruction.Segre.ProjectiveCharts.SegreHomogeneousChart R p.1 p.2))).inv
  have hm : e (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreChartCoordinate R p.1 p.2 (ULift.up a, ULift.up b)) =
      e (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreChartCoordinate R p.1 p.2 (ULift.up a, p.2)) *
        e (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreChartCoordinate R p.1 p.2 (p.1, ULift.up b)) :=
    (congrArg e (AbelianModuli.HilbertConstruction.Segre.ChartCoordinates.segreChartCoordinate_entry R p.1 (ULift.up a) p.2 (ULift.up b))).trans
      (map_mul e.hom _ _)
  exact ht.trans (hm.trans (congrArg₂ (fun x y => x * y) hr hc).symm)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Segre.ChartRatioIdentity
