import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.CoordinateSubstitution
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Dual.CoordinateTransform
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedCoordinateEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ConfigurationEvaluation

/-! # Coordinate Change Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.CoordinateChangeEvaluation

noncomputable section

/-! A common invertible change of point coordinates induces an
invertible substitution in each homogeneous polynomial degree.
Polynomial evaluation transforms by precomposing with this explicit
substitution, with the transpose convention fixed by dual pairing. -/
universe u v
variable {R : Type u} [CommRing R] {n : ℕ}

def polynomialLinearDegreeEquiv
    (e : (Fin (n + 1) →₀ R) ≃ₗ[R] (Fin (n + 1) →₀ R)) (d : ℕ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d ≃ₗ[R] HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d where
  toFun p := ⟨Linear.CoordinateSubstitution.polynomialLinearSubstitution e.toLinearMap p.val,
    Linear.CoordinateSubstitution.polynomialLinearSubstitution_homogeneous _ p.property⟩
  invFun p := ⟨Linear.CoordinateSubstitution.polynomialLinearSubstitution e.symm.toLinearMap p.val,
    Linear.CoordinateSubstitution.polynomialLinearSubstitution_homogeneous _ p.property⟩
  left_inv p := by
    apply Subtype.ext
    have he : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro a
      exact e.symm_apply_apply a
    have h := Linear.CoordinateSubstitution.polynomialLinearSubstitution_comp e.toLinearMap e.symm.toLinearMap
    rw [he, Linear.CoordinateSubstitution.polynomialLinearSubstitution_id] at h
    exact AlgHom.congr_fun h p.val
  right_inv p := by
    apply Subtype.ext
    have he : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro a
      exact e.apply_symm_apply a
    have h := Linear.CoordinateSubstitution.polynomialLinearSubstitution_comp e.symm.toLinearMap e.toLinearMap
    rw [he, Linear.CoordinateSubstitution.polynomialLinearSubstitution_id] at h
    exact AlgHom.congr_fun h p.val
  map_add' p q := Subtype.ext (map_add _ _ _)
  map_smul' r p := Subtype.ext (map_smul _ _ _)

theorem linearCoordinatePolynomial_aeval_pairing (v : Fin (n + 1) → R)
    (a : Fin (n + 1) →₀ R) :
    MvPolynomial.aeval v (Linear.CoordinateSubstitution.linearCoordinatePolynomial a) =
      (Finsupp.llift R R R (Fin (n + 1)) v) a := by
  let f : (Fin (n + 1) →₀ R) →ₗ[R] R :=
    (MvPolynomial.aeval v).toLinearMap.comp Linear.CoordinateSubstitution.linearCoordinatePolynomial
  have hf : (Finsupp.llift R R R (Fin (n + 1))).symm f = v := by
    funext i
    change MvPolynomial.aeval v (Linear.CoordinateSubstitution.linearCoordinatePolynomial (Finsupp.single i 1)) = v i
    rw [Linear.CoordinateSubstitution.linearCoordinatePolynomial_single, one_smul, MvPolynomial.aeval_X]
  change f a = _
  rw [← hf, LinearEquiv.apply_symm_apply]

theorem pointCoordinateSubstitution_evaluation
    (T : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R))
    (v : Fin (n + 1) → R) (p : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.aeval v (Linear.CoordinateSubstitution.polynomialLinearSubstitution (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).toLinearMap p) =
      MvPolynomial.aeval (T v) p := by
  let g := GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).toLinearMap
  have hv : GradedCoordinateEvaluation.gradedCoordinateValues g (algebraMap R R) v = T v := by
    funext i
    change MvPolynomial.aeval v
      (Linear.CoordinateSubstitution.polynomialLinearSubstitution (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).toLinearMap (MvPolynomial.X i)) = T v i
    rw [Linear.CoordinateSubstitution.polynomialLinearSubstitution_X, linearCoordinatePolynomial_aeval_pairing]
    exact Dual.CoordinateTransform.pointCoordinateCoefficientTransform_values T v i
  have h := GradedCoordinateEvaluation.gradedCoordinateEvaluation_apply g
    (fun r => (Linear.CoordinateSubstitution.polynomialLinearSubstitution (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T).toLinearMap).commutes r)
    (algebraMap R R) v p
  rw [hv] at h
  exact h

def pointCoordinatePolynomialDegreeEquiv
    (T : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) (d : ℕ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d ≃ₗ[R] HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d :=
  polynomialLinearDegreeEquiv (Dual.CoordinateTransform.pointCoordinateCoefficientTransform T) d

theorem homogeneousConfigurationEvaluation_linearCoordinates {ι : Type v}
    (w : ι → Fin (n + 1) → R) (d : ℕ)
    (T : (Fin (n + 1) → R) ≃ₗ[R] (Fin (n + 1) → R)) :
    Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation (fun c => T (w c)) d =
      (Homogeneous.ConfigurationEvaluation.homogeneousConfigurationEvaluation w d).comp (pointCoordinatePolynomialDegreeEquiv T d).toLinearMap := by
  apply LinearMap.ext
  intro p
  funext c
  exact (pointCoordinateSubstitution_evaluation T (w c) p.val).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.CoordinateChangeEvaluation
