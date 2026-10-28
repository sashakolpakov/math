import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GlobalFunctionsMatrix

/-! # Global Functions Identity Model -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GlobalFunctionsIdentityModel

noncomputable section

/-! The uniform projective global-functions matrix also models the original coefficient ring, after identifying identity coefficient extension. -/

open _root_.AlgebraicGeometry

universe u

theorem extendedHomogeneousIdeal_sameRing {R : Type u} [CommRing R] {n : ℕ}
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) : HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := R) I = I := by
  apply HomogeneousIdeal.ext
  change I.toIdeal.map (MvPolynomial.map (algebraMap R R)) = I.toIdeal
  have h : MvPolynomial.map (algebraMap R R) = RingHom.id (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) := by
    apply RingHom.ext
    intro p
    exact MvPolynomial.map_id p
  rw [h, Ideal.map_id]

theorem flatProjectiveCoordinate_globalFunctions_uniform_matrix_with_identity
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) [Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))] :
    ∃ (m k : ℕ) (B : Matrix (ULift.{u} (Fin k) ⊕ ULift.{u} (Fin m)) (ULift.{u} (Fin m)) R),
      Nonempty (Coefficient.AlgebraPresheaf.coefficientAlgebraSections
        (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))) ⊤ ≃ₗ[R] (Matrix.toLin' B).ker) ∧
      ∀ (A : Type u) [CommRing A] [Algebra R A],
        Nonempty (Coefficient.AlgebraPresheaf.coefficientAlgebraSections
          (Affine.ChartCoefficientSections.schemeGlobalCoefficient (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)))) ⊤ ≃ₗ[A]
          (Matrix.toLin' (B.map (algebraMap R A))).ker) := by
  obtain ⟨m, k, B, hB⟩ := GlobalFunctionsMatrix.flatProjectiveCoordinate_globalFunctions_uniform_matrix I
  refine ⟨m, k, B, ?_, hB⟩
  have H := hB R
  have hi : HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := R) I = I := extendedHomogeneousIdeal_sameRing I
  have hm : B.map (algebraMap R R) = B := rfl
  rw [hi, hm] at H
  exact H

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GlobalFunctionsIdentityModel
