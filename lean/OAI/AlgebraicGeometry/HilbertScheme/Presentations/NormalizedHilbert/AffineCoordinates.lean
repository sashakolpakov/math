import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.PolynomialCanonicalCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.UniversalIdeal
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.NormalizedChartPoint
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialIdealRingMap

/-! # Affine Coordinates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.AffineCoordinates.GradedHilbert

noncomputable section

/-! Actual canonical homogeneous coordinates of normalized Hilbert families
on affine tests, and recovery of the original coefficient matrix. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.NormalizedChartPoint.Grassmannian

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable {S : Scheme.{u}} {R : Type u} [CommRing R]
variable (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (f : Spec (.of R) ⟶ S)

def affineChartMatrix (x : Over.mk f ⟶ Normalized.Chart.Grassmannian.normalizedChart a S) : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R :=
  (Normalized.AtlasMaps.Grassmannian.chartMatrix a S x).map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom

omit [Fintype ι] in
theorem affineChartMatrix_normalized (x : Over.mk f ⟶ Normalized.Chart.Grassmannian.normalizedChart a S) :
    Normalized.Matrices.Grassmannian.IsNormalized a (affineChartMatrix a f x) :=
  (Normalized.AtlasMaps.Grassmannian.chartMatrix_normalized a S x).map _

omit [Fintype ι] in
theorem affineChartMatrix_of_matrix (Q : Matrix ι (Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) R) (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q) :
    affineChartMatrix a f (Affine.NormalizedChartPoint.Grassmannian.affineNormalizedChartPoint f a Q hQ) = Q := by
  unfold affineChartMatrix
  rw [Affine.NormalizedChartPoint.Grassmannian.affineNormalizedChartPoint_matrix]
  ext i j
  exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id (Q i j)

theorem normalizedChart_pointIdeal (x : Over.mk f ⟶ Normalized.Chart.Grassmannian.normalizedChart a S) :
    Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal (Normalized.Chart.Grassmannian.normalizedChart a S)
      (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a (Normalized.Chart.Grassmannian.universalNormalizedMatrix a S)) x.left =
      Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a (affineChartMatrix a f x) := by
  change (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a (Normalized.Chart.Grassmannian.universalNormalizedMatrix a S)).map
    (Graded.BaseChange.GradedHilbert.gradedCoefficientMap (PointCoefficients.schemePointCoefficientMap x.left)) = _
  rw [Normalized.PolynomialIdealRingMap.GradedHilbert.normalizedPolynomialIdeal_map]
  congr 1
  rw [affineChartMatrix, Normalized.AtlasMaps.Grassmannian.chartMatrix, Normalized.Chart.Grassmannian.normalizedChartRepresentation_apply]
  rfl

variable [IsLocallyNoetherian S]

theorem normalizedHilbertNativeFamily_affine_coordinates (q : ℕ → ℕ)
    (x : Over.mk f ⟶ Normalized.Chart.Grassmannian.normalizedChart a S)
    (hx : x ∈ (Chart.GradedHilbert.normalizedHilbertChartSubfunctor a S q).obj (.op (Over.mk f))) :
    Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f (IntrinsicFamily.GradedHilbert.normalizedHilbertNativeFamily a S q x hx) =
      Projective.Saturation.GradedHilbert.projectiveSaturation (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a (affineChartMatrix a f x)) := by
  have h := Global.PolynomialCanonicalCoordinates.GradedHilbert.globalPolynomialFamily_canonical_coordinates (Normalized.Chart.Grassmannian.normalizedChart a S)
    (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a (Normalized.Chart.Grassmannian.universalNormalizedMatrix a S)) x.left f x.w
    (IntrinsicFamily.GradedHilbert.normalizedHilbertNativeFamily a S q x hx) (BoundedHilbert.UniversalIdeal.GradedHilbert.normalizedHilbertNativeFamily_original_ker a S q x hx)
  exact h.trans (congrArg Projective.Saturation.GradedHilbert.projectiveSaturation (normalizedChart_pointIdeal a f x))

theorem boundedHilbertUniversalFamily_affine_chart_coordinates (q : ℕ → ℕ)
    (x : Over.mk f ⟶ Chart.GradedHilbert.normalizedHilbertChart a S q) :
    Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f
      (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (x ≫ BoundedHilbert.ChartPullback.GradedHilbert.boundedHilbertChartOverMap a S q)
        (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S q)) =
      Projective.Saturation.GradedHilbert.projectiveSaturation (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a
        (affineChartMatrix a f (x ≫ Chart.GradedHilbert.normalizedHilbertChartInclusion a S q))) := by
  let y := x ≫ Chart.GradedHilbert.normalizedHilbertChartInclusion a S q
  have h := Global.PolynomialCanonicalCoordinates.GradedHilbert.globalPolynomialFamily_canonical_coordinates (Normalized.Chart.Grassmannian.normalizedChart a S)
    (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a (Normalized.Chart.Grassmannian.universalNormalizedMatrix a S)) y.left f y.w
    (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (x ≫ BoundedHilbert.ChartPullback.GradedHilbert.boundedHilbertChartOverMap a S q)
      (BoundedHilbert.UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S q))
    (BoundedHilbert.UniversalIdeal.GradedHilbert.boundedHilbertUniversalFamily_chart_ideal a S q x)
  exact h.trans (congrArg Projective.Saturation.GradedHilbert.projectiveSaturation (normalizedChart_pointIdeal a f y))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.AffineCoordinates.GradedHilbert
