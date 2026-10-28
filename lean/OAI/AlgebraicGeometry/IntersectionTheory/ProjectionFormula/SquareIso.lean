import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GlobalProjective
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormAutomorphism
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeSupport

/-! # Square Iso -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SquareIso

noncomputable section

/-! An independent square tuple of homogeneous linear coordinates
defines an actual projective automorphism. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ConeSupport OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LinearFormBasis.GradedMap

theorem exists_equiv {n : ℕ} (L : Fin (n + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) (hL : LinearIndependent ℂ L) :
    ∃ e : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 ≃ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1,
      Projective.ConeSupport.coordinates L = LinearFormBasis.GradedMap.gradedHom e.toLinearMap := by
  obtain ⟨e, he⟩ := LinearFormBasis.extend L hL id Function.injective_id
  refine ⟨e, ?_⟩
  have ha : MvPolynomial.aeval (fun a => (L a).val) = LinearFormBasis.GradedMap.algebraHom e.toLinearMap := by
    apply MvPolynomial.algHom_ext
    intro a
    rw [MvPolynomial.aeval_X, LinearFormBasis.GradedMap.algebraHom_X]
    exact (congrArg Subtype.val (he a)).symm
  apply GradedRingHom.ext
  intro p
  exact DFunLike.congr_fun ha p

theorem map_isIso_of_eq {n : ℕ} (f : Foundations.Scheme.ProjectiveSpace.projectiveGrading n →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n)
    (e : Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1 ≃ₗ[ℂ] Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) (he : f = LinearFormBasis.GradedMap.gradedHom e.toLinearMap)
    (hf : HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) ≤
      (HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading n)).map f) : IsIso (Proj.map f hf) := by
  subst f
  exact (inferInstanceAs (IsIso (LinearFormAutomorphism.iso e).hom))

theorem isIso {n : ℕ} (L : Fin (n + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading n 1) (hL : LinearIndependent ℂ L)
    (h : ∀ x : Foundations.Scheme.ProjectiveSpace.projectiveSpace n, (𝟙 (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) x ∈ Projective.BasicOpen.RationalProjection.domain (Projective.ConeSupport.coordinates L)) :
    IsIso (Projective.ProjectionRestriction.projection (Projective.ConeSupport.coordinates L) (𝟙 (Foundations.Scheme.ProjectiveSpace.projectiveSpace n)) h) := by
  obtain ⟨e, he⟩ := exists_equiv L hL
  have hf : HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) ≤
      (HomogeneousIdeal.irrelevant (Foundations.Scheme.ProjectiveSpace.projectiveGrading n)).map (Projective.ConeSupport.coordinates L) := by
    rw [he]
    exact LinearFormAutomorphism.irrelevant_le e
  rw [GlobalProjective.Projection.restriction (Projective.ConeSupport.coordinates L) hf, Category.id_comp]
  exact map_isIso_of_eq (Projective.ConeSupport.coordinates L) e he hf

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SquareIso
