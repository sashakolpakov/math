import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.AffineCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.PointIdeal

/-! # Field Polynomial -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.FieldPolynomial.GradedHilbert

noncomputable section

/-! The actual coefficient ideal and canonical saturated ideal at every
field-valued Hilbert-chart point have the specified polynomial. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable {S : Scheme.{u}} {K : Type u} [Field K]
variable (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (f : Spec (.of K) ⟶ S)

theorem normalizedHilbertChart_field_polynomial (q : ℕ → ℕ) (P : Polynomial ℚ)
    (hP : BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N q P) (x : Over.mk f ⟶ Normalized.Chart.Grassmannian.normalizedChart a S)
    (hx : x ∈ (Chart.GradedHilbert.normalizedHilbertChartSubfunctor a S q).obj (.op (Over.mk f))) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Normalized.PolynomialKernel.GradedHilbert.normalizedPolynomialIdeal a (AffineCoordinates.GradedHilbert.affineChartMatrix a f x)).toIdeal P := by
  have h := BoundedHilbert.PointIdeal.GradedHilbert.bounded_hilbert_point_ideal_polynomial (Normalized.Chart.Grassmannian.normalizedChart a S)
    (Chart.GradedHilbert.universalPolynomialGenerators a S) N (Chart.GradedHilbert.universalPolynomialGenerators_homogeneous a S)
    q P hP x hx (𝟙 (Spec (.of K)))
  rw [Category.id_comp] at h
  exact Eq.mp (congrArg
    (fun J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n) => Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial J.toIdeal P)
    (AffineCoordinates.GradedHilbert.normalizedChart_pointIdeal a f x)) h

theorem normalizedHilbertNativeFamily_field_polynomial [IsLocallyNoetherian S]
    (q : ℕ → ℕ) (P : Polynomial ℚ) (hP : BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N q P)
    (x : Over.mk f ⟶ Normalized.Chart.Grassmannian.normalizedChart a S)
    (hx : x ∈ (Chart.GradedHilbert.normalizedHilbertChartSubfunctor a S q).obj (.op (Over.mk f))) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f (IntrinsicFamily.GradedHilbert.normalizedHilbertNativeFamily a S q x hx)).toIdeal P := by
  rw [AffineCoordinates.GradedHilbert.normalizedHilbertNativeFamily_affine_coordinates]
  exact (Saturation.Polynomial.GradedHilbert.projectiveSaturation_hasHilbertPolynomial_iff _ P).mpr
    (normalizedHilbertChart_field_polynomial a f q P hP x hx)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.FieldPolynomial.GradedHilbert
