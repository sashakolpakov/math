import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.FieldPolynomial
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.FieldIdealRecovery
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.PolynomialKernelRecovery
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.ChartMatrixSections
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.ChartClassifyingMap

/-! # Field Injectivity -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.FieldInjectivity.GradedHilbert

noncomputable section

/-! In the uniform degree range, equal native field families determine
the same actual Grassmannian parameter across all normalized Hilbert charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.ChartClassifyingMap.Grassmannian

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {K : Type u} [Field K]

theorem normalizedHilbertNativeFamily_field_parameter_injective
    (a b : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (f : Spec (.of K) ⟶ S)
    (q : ℕ → ℕ) (P : Polynomial ℚ) (hP : BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N q P)
    (hN : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ N)
    (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat)
    (x : Over.mk f ⟶ Normalized.Chart.Grassmannian.normalizedChart a S) (y : Over.mk f ⟶ Normalized.Chart.Grassmannian.normalizedChart b S)
    (hx : x ∈ (Chart.GradedHilbert.normalizedHilbertChartSubfunctor a S q).obj (.op (Over.mk f)))
    (hy : y ∈ (Chart.GradedHilbert.normalizedHilbertChartSubfunctor b S q).obj (.op (Over.mk f)))
    (hF : IntrinsicFamily.GradedHilbert.normalizedHilbertNativeFamily a S q x hx = IntrinsicFamily.GradedHilbert.normalizedHilbertNativeFamily b S q y hy) :
    x ≫ Grassmannian.Gluing.grassmannianChartOverMap a S = y ≫ Grassmannian.Gluing.grassmannianChartOverMap b S := by
  have hs := congrArg (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f) hF
  rw [AffineCoordinates.GradedHilbert.normalizedHilbertNativeFamily_affine_coordinates, AffineCoordinates.GradedHilbert.normalizedHilbertNativeFamily_affine_coordinates] at hs
  have he : Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a (AffineCoordinates.GradedHilbert.affineChartMatrix a f x) =
      Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal b (AffineCoordinates.GradedHilbert.affineChartMatrix b f y) := by
    rw [Normalized.FieldIdealRecovery.GradedHilbert.normalizedFieldIdeal_eq_degreeGenerated_saturation a _ (AffineCoordinates.GradedHilbert.affineChartMatrix_normalized a f x)
      P (FieldPolynomial.GradedHilbert.normalizedHilbertChart_field_polynomial a f q P hP x hx) hN hr,
      Normalized.FieldIdealRecovery.GradedHilbert.normalizedFieldIdeal_eq_degreeGenerated_saturation b _ (AffineCoordinates.GradedHilbert.affineChartMatrix_normalized b f y)
      P (FieldPolynomial.GradedHilbert.normalizedHilbertChart_field_polynomial b f q P hP y hy) hN hr, hs]
  have hsections := congrArg
    (fun J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n) => J.map
      (Graded.BaseChange.GradedHilbert.gradedCoefficientMap (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) he
  rw [Normalized.PolynomialIdealRingMap.GradedHilbert.normalizedPolynomialIdeal_map, Normalized.PolynomialIdealRingMap.GradedHilbert.normalizedPolynomialIdeal_map,
    Affine.ChartMatrixSections.GradedHilbert.affineChartMatrix_map_sections, Affine.ChartMatrixSections.GradedHilbert.affineChartMatrix_map_sections] at hsections
  exact (Quotient.ChartClassifyingMap.Grassmannian.chartMaps_eq_iff_kernel_eq a b x y).mpr
    ((Normalized.PolynomialKernelRecovery.GradedHilbert.normalizedPolynomialIdeal_eq_iff_kernel_eq a b _ _
      (Normalized.AtlasMaps.Grassmannian.chartMatrix_normalized a S x) (Normalized.AtlasMaps.Grassmannian.chartMatrix_normalized b S y)).mp hsections)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.FieldInjectivity.GradedHilbert
