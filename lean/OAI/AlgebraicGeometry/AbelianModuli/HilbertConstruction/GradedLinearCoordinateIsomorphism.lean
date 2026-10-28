import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.CoordinateSubstitution
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedProjectiveIsomorphism

/-! # Graded Linear Coordinate Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedLinearCoordinateIsomorphism

noncomputable section

/-! Invertible coefficient transformations induce genuine isomorphisms
of projective schemes, through their inverse graded polynomial maps. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u v w
variable {R : Type (max u v w)} [CommRing R] {σ : Type v} {τ : Type w}
attribute [local instance] MvPolynomial.gradedAlgebra

def gradedLinearCoordinateMap (T : (σ →₀ R) →ₗ[R] (τ →₀ R)) :
    MvPolynomial.homogeneousSubmodule σ R →+*ᵍ MvPolynomial.homogeneousSubmodule τ R where
  __ := (Linear.CoordinateSubstitution.polynomialLinearSubstitution T).toRingHom
  map_mem h := Linear.CoordinateSubstitution.polynomialLinearSubstitution_homogeneous T h

theorem gradedLinearCoordinateMap_inverse (e : (σ →₀ R) ≃ₗ[R] (τ →₀ R)) :
    (gradedLinearCoordinateMap.{u, w, v} e.symm.toLinearMap).comp (gradedLinearCoordinateMap.{u, v, w} e.toLinearMap) =
      GradedRingHom.id (MvPolynomial.homogeneousSubmodule σ R) := by
  have he : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact e.symm_apply_apply x
  have h : (Linear.CoordinateSubstitution.polynomialLinearSubstitution e.symm.toLinearMap).comp
      (Linear.CoordinateSubstitution.polynomialLinearSubstitution e.toLinearMap) = AlgHom.id R _ := by
    rw [Linear.CoordinateSubstitution.polynomialLinearSubstitution_comp, he, Linear.CoordinateSubstitution.polynomialLinearSubstitution_id]
  apply GradedRingHom.ext
  intro p
  exact AlgHom.congr_fun h p

def linearCoordinateProjectiveIso (e : (σ →₀ R) ≃ₗ[R] (τ →₀ R)) :
    Proj (MvPolynomial.homogeneousSubmodule σ R) ≅ Proj (MvPolynomial.homogeneousSubmodule τ R) :=
  GradedProjectiveIsomorphism.gradedProjectiveIso (MvPolynomial.homogeneousSubmodule σ R) (MvPolynomial.homogeneousSubmodule τ R)
    (gradedLinearCoordinateMap.{u, v, w} e.toLinearMap) (gradedLinearCoordinateMap.{u, w, v} e.symm.toLinearMap)
    (gradedLinearCoordinateMap_inverse.{u, w, v} e.symm) (gradedLinearCoordinateMap_inverse.{u, v, w} e)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedLinearCoordinateIsomorphism
