import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.NoetherianFieldPolynomial
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.CoefficientPolynomialCriterion

/-! # Intrinsic Fiber Polynomial -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.IntrinsicFiberPolynomial.GradedHilbert

noncomputable section

/-! Canonical residue polynomials of a native family over any noetherian
affine test imply every canonical field polynomial and the exact Presentations predicate. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {S : Scheme.{u}} {n : ℕ}
variable (f : Spec (.of R) ⟶ S)
variable (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f)) (P : Polynomial ℚ)
variable (hP : ∀ p : PrimeSpectrum R, Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
  (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
    (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F))).toIdeal P)
include hP

theorem noetherian_canonical_field_polynomial {K : Type u} [Field K] (φ : R →+* K) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n (Spec.map (CommRingCat.ofHom φ) ≫ f)
      (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ) F)).toIdeal P := by
  let I := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F
  let : Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_flat n f F
  let : Algebra R K := φ.toAlgebra
  rw [Affine.HomogeneousCoordinateBaseChange.GradedHilbert.affineNativeHomogeneousIdeal_baseChange]
  exact Uniform.NoetherianFieldPolynomial.GradedHilbert.uniformFamily_field_hasHilbertPolynomial I (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_saturated n f F) P hP K

theorem noetherian_hasFiberHilbertPolynomial :
    Has.Core.HasFiberHilbertPolynomial (Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S n) F P := by
  apply Affine.CoefficientPolynomialCriterion.GradedHilbert.hasFiberHilbertPolynomial_of_affine_coefficients f F P
  intro K _ φ
  have h := noetherian_canonical_field_polynomial f F P hP φ
  rw [Affine.HomogeneousCoordinateBaseChange.GradedHilbert.affineNativeHomogeneousIdeal_baseChange] at h
  exact h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.IntrinsicFiberPolynomial.GradedHilbert
