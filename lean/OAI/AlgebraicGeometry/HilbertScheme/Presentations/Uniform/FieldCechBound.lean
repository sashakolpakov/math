import OAI.AlgebraicGeometry.HilbertScheme.Presentations.InfiniteFieldCechBound
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FieldExtensionCechDescent
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.Bound

/-! # Field Cech Bound -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FieldCechBound.GradedHilbert

noncomputable section

/-! Uniform graded Čech vanishing for saturated homogeneous coordinate ideals over all fields, with no coordinate-regularity hypothesis. -/

universe u

theorem saturated_cech_exact_uniform {K : Type u} [Field K] {n : ℕ}
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (hSat : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
    (P : Polynomial ℚ) (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P) :
    ∀ d : ℤ, (RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P : ℤ) ≤ d → ∀ q : ℕ,
      Cech.DimensionShift.ProjectiveCech.ModuleCechExactAt (σ := Fin (n + 1)) K (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n ⧸ I.toIdeal)
        (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d q := by
  let : Infinite (RatFunc K) := Infinite.of_injective _ (RatFunc.algebraMap_injective K)
  let J := ScalarExtension.GradedHilbert.scalarExtendedHomogeneousIdeal (L := RatFunc K) I
  have hSatJ : Hilbert.Polynomial.GradedHilbert.IsSaturated J.toIdeal := ScalarExtension.GradedHilbert.scalarExtendedIdeal_isSaturated I.toIdeal hSat
  have hPJ : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial J.toIdeal P := (Hilbert.ScalarExtension.GradedHilbert.hasHilbertPolynomial_scalarExtended_iff I P).mpr hP
  intro d hd q
  exact FieldExtensionCechDescent.GradedHilbert.coordinate_moduleCechExactAt_of_field_extension (L := RatFunc K) I d q
    (InfiniteFieldCechBound.GradedHilbert.saturated_cech_exact_infinite_field J hSatJ P hPJ d hd q)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FieldCechBound.GradedHilbert
