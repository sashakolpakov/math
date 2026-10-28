import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.ChartAlgebra
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.ChartMaps

/-! # Overlap Algebra -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.OverlapAlgebra.Grassmannian

noncomputable section

/-!
The two affine normalizations on an intersection of Plücker charts have
exactly the previously constructed Grassmannian transition matrix.
-/

open _root_.MvPolynomial _root_.HomogeneousLocalization

universe u v w

variable {R : Type u} [CommRing R]
variable {ι : Type v} {ν : Type w} [Fintype ι] [DecidableEq ι]

abbrev pluckerQuotientGrading := Homogeneous.Quotient.HomogeneousQuotient.quotientGrading (Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν))

def pluckerVariable (a : ι → ν) : pluckerQuotientGrading (R := R) (ι := ι) (ν := ν) 1 :=
  ⟨Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap (Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν)) (X a),
    (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap (Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν))).map_mem (isHomogeneous_X R a)⟩

abbrev pluckerDoubleChart (a b : ι → ν) :=
  Away (pluckerQuotientGrading (R := R) (ι := ι) (ν := ν))
    ((pluckerVariable (R := R) a).val * (pluckerVariable (R := R) b).val)

def pluckerOverlapLeft (a b : ι → ν) :
    ChartAlgebra.Grassmannian.pluckerHomogeneousChart (R := R) a →ₐ[R] pluckerDoubleChart (R := R) a b :=
  Homogeneous.ChartMaps.homogeneousOverlapLeft _ (pluckerVariable (R := R) b).property

def pluckerOverlapRight (a b : ι → ν) :
    ChartAlgebra.Grassmannian.pluckerHomogeneousChart (R := R) b →ₐ[R] pluckerDoubleChart (R := R) a b :=
  Homogeneous.ChartMaps.homogeneousOverlapRight _ (pluckerVariable (R := R) a).property

theorem pluckerOverlapLeft_coordinates (a b c : ι → ν) :
    pluckerOverlapLeft (R := R) a b
      (Polynomial.ChartPresentation.PolynomialProjective.affineChartMap (Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν)) a (X c)) =
      Homogeneous.ChartRatios.overlapRatioLeft (pluckerQuotientGrading (R := R) (ι := ι) (ν := ν))
        (pluckerVariable (R := R) a).property (pluckerVariable (R := R) b).property (pluckerVariable (R := R) c) := by
  rw [Polynomial.ChartPresentation.PolynomialProjective.affineChartMap_homogeneous _ _ (isHomogeneous_X R c)]
  exact Homogeneous.ChartMaps.homogeneousOverlapLeft_ratio (pluckerQuotientGrading (R := R) (ι := ι) (ν := ν)) (pluckerVariable (R := R) a).property (pluckerVariable (R := R) b).property
    (pluckerVariable (R := R) c)

theorem pluckerOverlapRight_coordinates (a b c : ι → ν) :
    pluckerOverlapRight (R := R) a b
      (Polynomial.ChartPresentation.PolynomialProjective.affineChartMap (Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν)) b (X c)) =
      Homogeneous.ChartRatios.overlapRatioRight (pluckerQuotientGrading (R := R) (ι := ι) (ν := ν))
        (pluckerVariable (R := R) a).property (pluckerVariable (R := R) b).property (pluckerVariable (R := R) c) := by
  rw [Polynomial.ChartPresentation.PolynomialProjective.affineChartMap_homogeneous _ _ (isHomogeneous_X R c)]
  exact Homogeneous.ChartMaps.homogeneousOverlapRight_ratio (pluckerQuotientGrading (R := R) (ι := ι) (ν := ν)) (pluckerVariable (R := R) a).property (pluckerVariable (R := R) b).property
    (pluckerVariable (R := R) c)

def pluckerOverlapMatrixLeft (a b : ι → ν) : Matrix ι ν (pluckerDoubleChart (R := R) a b) :=
  (ChartAlgebra.Grassmannian.pluckerHomogeneousChartPointEquiv a (pluckerOverlapLeft (R := R) a b)).val

def pluckerOverlapMatrixRight (a b : ι → ν) : Matrix ι ν (pluckerDoubleChart (R := R) a b) :=
  (ChartAlgebra.Grassmannian.pluckerHomogeneousChartPointEquiv b (pluckerOverlapRight (R := R) a b)).val

theorem pluckerOverlapMatrixLeft_minor (a b c : ι → ν) :
    Determinants.Grassmannian.maximalMinor (pluckerOverlapMatrixLeft (R := R) a b) c =
      Homogeneous.ChartRatios.overlapRatioLeft (pluckerQuotientGrading (R := R) (ι := ι) (ν := ν))
        (pluckerVariable (R := R) a).property (pluckerVariable (R := R) b).property (pluckerVariable (R := R) c) :=
  (ChartAlgebra.Grassmannian.pluckerHomogeneousChartPointEquiv_minor a c (pluckerOverlapLeft (R := R) a b)).trans
    (pluckerOverlapLeft_coordinates (R := R) a b c)

theorem pluckerOverlapMatrixRight_minor (a b c : ι → ν) :
    Determinants.Grassmannian.maximalMinor (pluckerOverlapMatrixRight (R := R) a b) c =
      Homogeneous.ChartRatios.overlapRatioRight (pluckerQuotientGrading (R := R) (ι := ι) (ν := ν))
        (pluckerVariable (R := R) a).property (pluckerVariable (R := R) b).property (pluckerVariable (R := R) c) :=
  (ChartAlgebra.Grassmannian.pluckerHomogeneousChartPointEquiv_minor b c (pluckerOverlapRight (R := R) a b)).trans
    (pluckerOverlapRight_coordinates (R := R) a b c)

theorem pluckerOverlapMatrixLeft_pivot_isUnit (a b : ι → ν) :
    IsUnit (Determinants.Grassmannian.maximalMinor (pluckerOverlapMatrixLeft (R := R) a b) b) := by
  rw [pluckerOverlapMatrixLeft_minor]
  exact Homogeneous.ChartRatios.overlapRatio_pivot_isUnit (pluckerQuotientGrading (R := R) (ι := ι) (ν := ν)) (pluckerVariable (R := R) a).property (pluckerVariable (R := R) b).property

theorem pluckerOverlapMatrix_cross (a b c : ι → ν) :
    Determinants.Grassmannian.maximalMinor (pluckerOverlapMatrixLeft (R := R) a b) b *
        Determinants.Grassmannian.maximalMinor (pluckerOverlapMatrixRight (R := R) a b) c =
      Determinants.Grassmannian.maximalMinor (pluckerOverlapMatrixLeft (R := R) a b) c := by
  rw [pluckerOverlapMatrixLeft_minor, pluckerOverlapMatrixRight_minor, pluckerOverlapMatrixLeft_minor]
  exact Homogeneous.ChartRatios.overlapRatio_cross (pluckerQuotientGrading (R := R) (ι := ι) (ν := ν)) (pluckerVariable (R := R) a).property (pluckerVariable (R := R) b).property (pluckerVariable (R := R) c)

theorem pluckerOverlapMatrix_transition (a b : ι → ν) :
    pluckerOverlapMatrixRight (R := R) a b = Normalized.Matrices.Grassmannian.normalizeColumns b (pluckerOverlapMatrixLeft (R := R) a b) := by
  have hu := pluckerOverlapMatrixLeft_pivot_isUnit (R := R) a b
  apply Determinants.Grassmannian.maximalMinors_injective_on_normalized b _ _
    (ChartAlgebra.Grassmannian.pluckerHomogeneousChartPointEquiv b (pluckerOverlapRight (R := R) a b)).property
    (Normalized.Matrices.Grassmannian.normalizeColumns_normalized b _ hu)
  intro c
  apply hu.mul_left_cancel
  exact (pluckerOverlapMatrix_cross (R := R) a b c).trans (Determinants.Grassmannian.maximalMinor_normalize b c _ hu).symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.OverlapAlgebra.Grassmannian
