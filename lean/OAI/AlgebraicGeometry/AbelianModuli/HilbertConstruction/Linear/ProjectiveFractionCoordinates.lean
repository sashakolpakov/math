import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedFractionMapNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.LinearCoordinateIsomorphism

/-! # Projective Fraction Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.ProjectiveFractionCoordinates

noncomputable section

/-! Linear projective coordinate changes have the expected transformed
coordinate values and explicit local homogeneous-fraction formula. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R B : Type u} [CommRing R] [CommRing B] {n : ℕ}

theorem linearCoordinatePolynomial_evaluation (c : R →+* B) (v : Fin (n + 1) → B)
    (a : Fin (n + 1) →₀ R) :
    MvPolynomial.eval₂Hom c v (CoordinateSubstitution.linearCoordinatePolynomial a) =
      ∑ i ∈ a.support, c (a i) * v i := by
  simp only [CoordinateSubstitution.linearCoordinatePolynomial, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']

theorem gradedLinearCoordinateValues_eq (T : (Fin (n + 1) →₀ R) →ₗ[R] (Fin (n + 1) →₀ R))
    (c : R →+* B) (v : Fin (n + 1) → B) (j : Fin (n + 1)) :
    GradedCoordinateEvaluation.gradedCoordinateValues (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap T) c v j =
      ∑ i ∈ (T (Finsupp.single j 1)).support, c (T (Finsupp.single j 1) i) * v i := by
  change MvPolynomial.eval₂Hom c v (CoordinateSubstitution.polynomialLinearSubstitution T (MvPolynomial.X j)) = _
  rw [CoordinateSubstitution.polynomialLinearSubstitution_X]
  exact linearCoordinatePolynomial_evaluation c v _

variable {X : Scheme.{u}}

theorem affineLinearCoordinateIso_fraction
    (e : (Fin (n + 1) →₀ R) ≃ₗ[R] (Fin (n + 1) →₀ R))
    (c : R →+* Γ(X, ⊤)) (v : Fin (n + 1) → Γ(X, ⊤))
    (f : Projective.ProjectivePresentations.coordinateRing R n) (d : ℕ) (hfd : f ∈ Projective.ProjectivePresentations.coordinateGrading R n d) (hd : 0 < d)
    (hf : IsUnit (MvPolynomial.eval₂Hom c
      (GradedCoordinateEvaluation.gradedCoordinateValues (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap e.symm.toLinearMap) c v) f))
    (hg : IsUnit (MvPolynomial.eval₂Hom c v (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap e.symm.toLinearMap f))) :
    Chart.OverlapMaps.projectiveFractionMap c v (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap e.symm.toLinearMap f) hg d
        ((GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap e.symm.toLinearMap).map_mem hfd) hd ≫
      (Relative.LinearCoordinateIsomorphism.affineLinearCoordinateIso n e).hom.left =
    Chart.OverlapMaps.projectiveFractionMap c (GradedCoordinateEvaluation.gradedCoordinateValues (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap e.symm.toLinearMap) c v)
      f hf d hfd hd :=
  GradedFractionMapNaturality.projectiveFractionMap_gradedMap (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap e.symm.toLinearMap)
    (fun r => (CoordinateSubstitution.polynomialLinearSubstitution e.symm.toLinearMap).commutes r)
    (GradedProjectiveIsomorphism.gradedMap_irrelevant_of_inverse _ _ _ _ (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap_inverse e))
    c v f d hfd hd hf hg

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.ProjectiveFractionCoordinates
