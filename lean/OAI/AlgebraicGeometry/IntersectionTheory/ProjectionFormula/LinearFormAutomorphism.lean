import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormBasis
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearChart

/-! # Linear Form Automorphism -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormAutomorphism

noncomputable section

/-! Automorphisms of the space of linear forms induce actual
graded-ring and projective-scheme automorphisms. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormBasis.GradedMap

variable {n : ℕ} (e : (Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) ≃ₗ[ℂ] (Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1))

theorem graded_inverse : (LinearFormBasis.GradedMap.gradedHom e.toLinearMap).comp (LinearFormBasis.GradedMap.gradedHom e.symm.toLinearMap) =
    GradedRingHom.id (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) := by
  rw [← LinearFormBasis.GradedMap.gradedHom_comp]
  have he : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro p
    exact e.apply_symm_apply p
  rw [he, LinearFormBasis.GradedMap.gradedHom_id]

def algebraEquiv : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n ≃ₐ[ℂ] Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing n where
  __ := LinearFormBasis.GradedMap.algebraHom e.toLinearMap
  invFun := LinearFormBasis.GradedMap.algebraHom e.symm.toLinearMap
  left_inv p := DFunLike.congr_fun (graded_inverse e.symm) p
  right_inv p := DFunLike.congr_fun (graded_inverse e) p

theorem irrelevant_le : HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) ≤
    (HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading n)).map (LinearFormBasis.GradedMap.gradedHom e.toLinearMap) :=
  Projective.LinearChart.Automorphism.irrelevant_le_of_inverse _ _ (graded_inverse e)

def map : Foundations.Scheme.ProjectiveSpace.projectiveSpace n ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n := Proj.map (LinearFormBasis.GradedMap.gradedHom e.toLinearMap) (irrelevant_le e)

theorem map_inverse : LinearFormAutomorphism.map e ≫ LinearFormAutomorphism.map e.symm = 𝟙 (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) := by
  unfold LinearFormAutomorphism.map
  rw [← Proj.map_comp]
  simp only [graded_inverse, Proj.map_id]

def iso : Foundations.Scheme.ProjectiveSpace.projectiveSpace n ≅ Foundations.Scheme.ProjectiveSpace.projectiveSpace n where
  hom := LinearFormAutomorphism.map e
  inv := LinearFormAutomorphism.map e.symm
  hom_inv_id := map_inverse e
  inv_hom_id := map_inverse e.symm

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormAutomorphism
