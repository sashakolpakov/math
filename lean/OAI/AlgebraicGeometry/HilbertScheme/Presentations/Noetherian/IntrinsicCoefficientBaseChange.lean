import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.IntrinsicFiberPolynomial
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.CoefficientComposition

/-! # Intrinsic Coefficient Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.IntrinsicCoefficientBaseChange.GradedHilbert

noncomputable section

/-! The canonical residue-polynomial condition of a native family over a
noetherian affine ring persists under arbitrary coefficient-ring base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R A : Type u} [CommRing R] [IsNoetherianRing R] [CommRing A]
variable {S : Scheme.{u}} {n : ℕ}

theorem noetherian_canonical_residue_polynomial_baseChange
    (f : Spec (.of R) ⟶ S) (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f))
    (P : Polynomial ℚ) (hP : ∀ p : PrimeSpectrum R, Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
        (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F))).toIdeal P)
    (φ : R →+* A) (p : PrimeSpectrum A) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField)
      (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n (Spec.map (CommRingCat.ofHom φ) ≫ f)
        (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap f φ) F)))).toIdeal P := by
  let I := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n f F
  let : Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_flat n f F
  let ψ : A →+* p.asIdeal.ResidueField := algebraMap A p.asIdeal.ResidueField
  let : Algebra R p.asIdeal.ResidueField := (ψ.comp φ).toAlgebra
  rw [Affine.HomogeneousCoordinateBaseChange.GradedHilbert.affineNativeHomogeneousIdeal_baseChange]
  change Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Projective.Saturation.GradedHilbert.projectiveSaturation
    ((Projective.Saturation.GradedHilbert.projectiveSaturation (I.map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ))).map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap ψ))).toIdeal P
  rw [Saturation.CoefficientComposition.GradedHilbert.projectiveSaturation_coefficient_comp]
  exact Uniform.NoetherianFieldPolynomial.GradedHilbert.uniformFamily_field_hasHilbertPolynomial I (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_saturated n f F)
    P hP p.asIdeal.ResidueField

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.IntrinsicCoefficientBaseChange.GradedHilbert
