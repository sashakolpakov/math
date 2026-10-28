import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.FieldPolynomial
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.HomogeneousCoordinateBaseChange

/-! # Residue Polynomial -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.ResiduePolynomial.GradedHilbert

noncomputable section

/-! Canonical residue-fiber polynomials of the actual normalized Hilbert
family on arbitrary affine test rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable {S : Scheme.{u}} [IsLocallyNoetherian S] {R : Type u} [CommRing R]

theorem normalizedHilbertNativeFamily_residue_polynomial
    (a : ι → Homogeneous.CoordinateBasis.GradedHilbert.DegreeIndex.{u} n N) (f : Spec (.of R) ⟶ S)
    (q : ℕ → ℕ) (P : Polynomial ℚ) (hP : BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N q P)
    (x : Over.mk f ⟶ Normalized.Chart.Grassmannian.normalizedChart a S)
    (hx : x ∈ (Chart.GradedHilbert.normalizedHilbertChartSubfunctor a S q).obj (.op (Over.mk f)))
    (p : PrimeSpectrum R) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
      (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f (IntrinsicFamily.GradedHilbert.normalizedHilbertNativeFamily a S q x hx)))).toIdeal P := by
  let g := Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f (algebraMap R p.asIdeal.ResidueField)
  have h := FieldPolynomial.GradedHilbert.normalizedHilbertNativeFamily_field_polynomial a _ q P hP (g ≫ x)
    ((Chart.GradedHilbert.normalizedHilbertChartSubfunctor a S q).map g.op hx)
  rw [IntrinsicFamily.GradedHilbert.normalizedHilbertNativeFamily_baseChange, Affine.HomogeneousCoordinateBaseChange.GradedHilbert.affineNativeHomogeneousIdeal_baseChange] at h
  exact h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.NormalizedHilbert.ResiduePolynomial.GradedHilbert
