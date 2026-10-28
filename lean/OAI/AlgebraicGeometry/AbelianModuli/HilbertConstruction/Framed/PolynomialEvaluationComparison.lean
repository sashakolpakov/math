import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Normalized.PolynomialCoordinateFrame
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SurjectiveFunctionalKernelComparison

/-! # Polynomial Evaluation Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.PolynomialEvaluationComparison

noncomputable section

/-! On a normalized projective point, evaluating canonical polynomial
sections in any actual fiber frame differs from literal polynomial
evaluation by one unit, uniformly for every degree-d polynomial. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] {n : ℕ}
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ)
variable (x : Spec (.of R) ⟶ Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
variable (hx : x ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) = 𝟙 _)
variable (e : ((ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).pullback x).sheaf ≅ Line.Bundles.structureModule (Spec (.of R)))

def framedHomogeneousPolynomialEvaluation : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d →ₗ[R] R :=
  (Affine.FramedSectionEvaluation.affineFramedSectionEvaluation (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
    (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d) x hx e).comp (SaturatedPolynomialSectionMap.homogeneousPolynomialTwistingSectionMap I d)

theorem framedHomogeneousPolynomialEvaluation_apply (p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d) :
    framedHomogeneousPolynomialEvaluation I d x hx e p =
      Affine.FramedSectionEvaluation.affineFramedSectionValue (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d) x e
        (Homogeneous.PolynomialSectionNonvanishing.coordinateQuotientActualTwistingSection I d ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).mkQ p)) := rfl

theorem framedPolynomialEvaluation_eq_unit_mul (hd : 0 < d)
    (v : Fin (n + 1) → R) (i : Fin (n + 1)) (hi : v i = 1)
    (hv : x ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I = AffineProjective.CoordinateMaps.affineProjectiveCoordinateMap (.of R) R v i hi) :
    ∃ a : Rˣ, ∀ p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d,
      framedHomogeneousPolynomialEvaluation I d x hx e p =
        (a : R) * MvPolynomial.eval₂Hom (algebraMap R R) v p.val := by
  let f : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d →ₗ[R] R := (MvPolynomial.aeval v).toLinearMap.comp (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d).subtype
  let g := framedHomogeneousPolynomialEvaluation I d x hx e
  let p₀ : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d := Normalized.PolynomialCoordinateFrame.homogeneousCoordinatePower i d
  have hp₀ : f p₀ = 1 := by
    change MvPolynomial.eval₂Hom (algebraMap R R) v (MvPolynomial.X i ^ d) = 1
    rw [map_pow, MvPolynomial.eval₂Hom_X', hi, one_pow]
  have hker : f.ker ≤ g.ker := by
    intro p hp
    change framedHomogeneousPolynomialEvaluation I d x hx e p = 0
    rw [framedHomogeneousPolynomialEvaluation_apply, Affine.FramedEvaluationZero.affineFramedSectionValue_eq_zero_iff]
    exact (Normalized.PolynomialSectionEvaluation.polynomialSection_pullback_zero_iff_normalized_evaluation I p x v i hi hv).mpr hp
  have hu : IsUnit (g p₀) := Normalized.PolynomialCoordinateFrame.normalizedPolynomialCoordinate_framedValue_isUnit I d hd x v i hi hv e
  obtain ⟨a, ha⟩ := hu
  refine ⟨a, fun p => ?_⟩
  calc
    g p = f p * g p₀ := SurjectiveFunctionalKernelComparison.linearFunctional_factor_of_kernel_le f g hker p₀ hp₀ p
    _ = (a : R) * f p := by rw [← ha, mul_comm]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.PolynomialEvaluationComparison
