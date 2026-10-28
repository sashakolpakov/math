import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CanonicalFiberPolynomialCriterion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.HomogeneousCoordinateBaseChange

/-! # Coefficient Polynomial Criterion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.CoefficientPolynomialCriterion.GradedHilbert

noncomputable section

/-! The exact native fiber-polynomial condition on an affine test follows
from the canonical homogeneous ideals under all field coefficient maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} {R : Type u} [CommRing R] {n : ℕ}

theorem hasFiberHilbertPolynomial_of_affine_coefficients
    (a : Spec (CommRingCat.of R) ⟶ S)
    (F : Hilbert.Functor.Family (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a)) (P : Polynomial ℚ)
    (hP : ∀ (L : Type u) [Field L] (φ : R →+* L),
      Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Projective.Saturation.GradedHilbert.projectiveSaturation
        ((IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n a F).map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ))).toIdeal P) :
    Has.Core.HasFiberHilbertPolynomial (Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S n) F P := by
  apply CanonicalFiberPolynomialCriterion.GradedHilbert.hasFiberHilbertPolynomial_of_canonical_fibers F P
  intro L _ b
  obtain ⟨φ, rfl⟩ : ∃ φ : R →+* L, Spec.map (CommRingCat.ofHom φ) = b :=
    ⟨(Spec.preimage b).hom, Spec.map_preimage b⟩
  change Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n (Spec.map (CommRingCat.ofHom φ) ≫ a)
    (Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a φ) F)).toIdeal P
  rw [HomogeneousCoordinateBaseChange.GradedHilbert.affineNativeHomogeneousIdeal_baseChange]
  exact hP L φ

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.CoefficientPolynomialCriterion.GradedHilbert
