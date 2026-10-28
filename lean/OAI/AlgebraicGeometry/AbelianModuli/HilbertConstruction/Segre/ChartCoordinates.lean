import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ProjectiveCharts

/-! # Chart Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ChartCoordinates

noncomputable section

/-! Normalized matrix entries in the actual affine charts of the Segre equation scheme. -/

open _root_.MvPolynomial

universe u v w

variable (R : Type u) [CommRing R] {σ : Type v} {τ : Type w}

abbrev segreQuotientGrading := HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.quotientGrading (HomogeneousRelations.segreHomogeneousIdeal (σ := σ) (τ := τ) R)

def segreVariable (q : σ × τ) : segreQuotientGrading (σ := σ) (τ := τ) R 1 :=
  ⟨HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap (HomogeneousRelations.segreHomogeneousIdeal R) (X q),
    (HilbertScheme.Presentations.Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap (HomogeneousRelations.segreHomogeneousIdeal R)).map_mem (isHomogeneous_X R q)⟩

def segreChartCoordinate (i : σ) (j : τ) (q : σ × τ) : ProjectiveCharts.SegreHomogeneousChart R i j :=
  HilbertScheme.Presentations.Polynomial.ChartPresentation.PolynomialProjective.affineChartMap (HomogeneousRelations.segreHomogeneousIdeal R) (i, j) (X q)

theorem segreChartCoordinate_pivot (i : σ) (j : τ) :
    segreChartCoordinate R i j (i, j) = 1 := by
  apply (ProjectiveCharts.segreHomogeneousChartEquiv R i j).injective
  rw [map_one]
  exact (ProjectiveCharts.segreHomogeneousChartEquiv_map R i j (X (i, j))).trans
    (NormalizedCoordinates.segreChartEvaluation_pivot R i j)

theorem segreChartCoordinate_entry (i a : σ) (j b : τ) :
    segreChartCoordinate R i j (a, b) =
      segreChartCoordinate R i j (a, j) * segreChartCoordinate R i j (i, b) := by
  classical
  apply (ProjectiveCharts.segreHomogeneousChartEquiv R i j).injective
  simp only [map_mul, segreChartCoordinate, ProjectiveCharts.segreHomogeneousChartEquiv_variable]
  simp [NormalizedCoordinates.segreRowCoordinate, NormalizedCoordinates.segreColumnCoordinate]

theorem segreChartCoordinate_minor (i a c : σ) (j b d : τ) :
    segreChartCoordinate R i j (a, b) * segreChartCoordinate R i j (c, d) =
      segreChartCoordinate R i j (a, d) * segreChartCoordinate R i j (c, b) := by
  apply (ProjectiveCharts.segreHomogeneousChartEquiv R i j).injective
  simp only [map_mul, segreChartCoordinate, ProjectiveCharts.segreHomogeneousChartEquiv_variable]
  ring

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.ChartCoordinates
