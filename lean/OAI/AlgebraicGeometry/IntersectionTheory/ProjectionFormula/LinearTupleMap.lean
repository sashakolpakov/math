import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormBasis
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeSupport
import Mathlib.LinearAlgebra.Basis.Basic

/-! # Linear Tuple Map -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearTupleMap

noncomputable section

/-! A tuple of linear projection coordinates is the image of the
coordinate basis under an actual linear map. Independent tuples remain
independent after an invertible change of target coordinates. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormBasis OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormBasis.GradedMap OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeSupport

variable {m n : ℕ} (L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1)

def linear : Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1 →ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 := (LinearFormBasis.basis m).constr ℂ L

theorem coordinate (a : Fin (m + 1)) : linear L (LinearFormBasis.coordinate m a) = L a := by
  rw [← LinearFormBasis.basis_apply]
  exact (LinearFormBasis.basis m).constr_basis ℂ L a

theorem injective (hL : LinearIndependent ℂ L) : Function.Injective (linear L) :=
  (LinearFormBasis.basis m).injective_constr_of_linearIndependent hL

theorem graded : LinearFormBasis.GradedMap.gradedHom (linear L) = Projective.ConeSupport.coordinates L := by
  apply GradedRingHom.ext
  intro p
  have he : LinearFormBasis.GradedMap.algebraHom (linear L) = MvPolynomial.aeval (fun a => (L a).val) := by
    apply MvPolynomial.algHom_ext
    intro a
    rw [LinearFormBasis.GradedMap.algebraHom_X, MvPolynomial.aeval_X, coordinate]
  exact DFunLike.congr_fun he p

def precompose (e : Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1 ≃ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1) :
    Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 := fun a => linear L (e (LinearFormBasis.coordinate m a))

theorem precompose_independent (hL : LinearIndependent ℂ L)
    (e : Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1 ≃ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1) : LinearIndependent ℂ (precompose L e) := by
  have hi := (LinearFormBasis.basis m).linearIndependent.map' ((linear L).comp e.toLinearMap)
    (LinearMap.ker_eq_bot.mpr ((LinearTupleMap.injective L hL).comp e.injective))
  change LinearIndependent ℂ (fun a => linear L (e (LinearFormBasis.coordinate m a)))
  simpa only [Function.comp_def, LinearFormBasis.basis_apply, LinearMap.comp_apply, LinearEquiv.coe_coe] using hi

theorem precompose_coordinates (e : Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1 ≃ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1) :
    Projective.ConeSupport.coordinates (precompose L e) = (Projective.ConeSupport.coordinates L).comp (LinearFormBasis.GradedMap.gradedHom e.toLinearMap) := by
  change LinearFormBasis.GradedMap.gradedHom ((linear L).comp e.toLinearMap) = _
  rw [LinearFormBasis.GradedMap.gradedHom_comp, graded]

theorem postcompose_coordinates (e : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 ≃ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) :
    Projective.ConeSupport.coordinates (fun a => e (L a)) = (LinearFormBasis.GradedMap.gradedHom e.toLinearMap).comp (Projective.ConeSupport.coordinates L) := by
  have he : linear (fun a => e (L a)) = e.toLinearMap.comp (linear L) := by
    apply (LinearFormBasis.basis m).ext
    intro a
    rw [LinearFormBasis.basis_apply, coordinate, LinearMap.comp_apply, coordinate]
    rfl
  rw [← graded, he, LinearFormBasis.GradedMap.gradedHom_comp, graded]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearTupleMap
