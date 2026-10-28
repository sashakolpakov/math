import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.LinearProjectiveIdentity

/-! # Projective Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.ProjectiveComposition

noncomputable section

/-! Actual linear projective coordinate maps compose as their
coefficient transformations do, and ignore a common unit scalar
in the inverse coefficient map. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {n : ℕ}

theorem gradedLinearCoordinateMap_comp
    (f g : (Fin (n + 1) →₀ R) →ₗ[R] (Fin (n + 1) →₀ R)) :
    (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap g).comp (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap f) = GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap (g.comp f) := by
  apply GradedRingHom.ext
  intro p
  exact AlgHom.congr_fun (CoordinateSubstitution.polynomialLinearSubstitution_comp f g) p

theorem affineLinearCoordinateIso_trans
    (e f : (Fin (n + 1) →₀ R) ≃ₗ[R] (Fin (n + 1) →₀ R)) :
    (Relative.LinearCoordinateIsomorphism.affineLinearCoordinateIso n (e.trans f)).hom =
      (Relative.LinearCoordinateIsomorphism.affineLinearCoordinateIso n e).hom ≫ (Relative.LinearCoordinateIsomorphism.affineLinearCoordinateIso n f).hom := by
  apply Over.OverMorphism.ext
  change Proj.map (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap (e.trans f).symm.toLinearMap) _ =
    Proj.map (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap e.symm.toLinearMap) _ ≫
      Proj.map (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap f.symm.toLinearMap) _
  have h : (e.trans f).symm.toLinearMap = e.symm.toLinearMap.comp f.symm.toLinearMap := by
    ext x
    rfl
  simp only [← Proj.map_comp, gradedLinearCoordinateMap_comp, h]

theorem affineLinearCoordinateIso_symm_hom
    (e : (Fin (n + 1) →₀ R) ≃ₗ[R] (Fin (n + 1) →₀ R)) :
    (Relative.LinearCoordinateIsomorphism.affineLinearCoordinateIso n e.symm).hom = (Relative.LinearCoordinateIsomorphism.affineLinearCoordinateIso n e).inv := rfl

theorem affineLinearCoordinateIso_eq_of_inverse_unit_smul
    (e f : (Fin (n + 1) →₀ R) ≃ₗ[R] (Fin (n + 1) →₀ R)) (a : Rˣ)
    (h : e.symm.toLinearMap = (a : R) • f.symm.toLinearMap) :
    (Relative.LinearCoordinateIsomorphism.affineLinearCoordinateIso n e).hom = (Relative.LinearCoordinateIsomorphism.affineLinearCoordinateIso n f).hom := by
  have hscalar : (f.symm.trans e).symm.toLinearMap = (a : R) • LinearMap.id := by
    apply LinearMap.ext
    intro x
    change f (e.symm x) = (a : R) • x
    have hx : e.symm x = (a : R) • f.symm x := LinearMap.congr_fun h x
    rw [hx, f.map_smul, f.apply_symm_apply]
  have hz : (Relative.LinearCoordinateIsomorphism.affineLinearCoordinateIso n (f.symm.trans e)).hom = 𝟙 _ :=
    Over.OverMorphism.ext (Scalar.LinearProjectiveIdentity.affineLinearCoordinateIso_eq_id_of_inverse_scalar (f.symm.trans e) a hscalar)
  rw [affineLinearCoordinateIso_trans, affineLinearCoordinateIso_symm_hom] at hz
  apply (cancel_epi (Relative.LinearCoordinateIsomorphism.affineLinearCoordinateIso n f).inv).mp
  rw [(Relative.LinearCoordinateIsomorphism.affineLinearCoordinateIso n f).inv_hom_id]
  exact hz

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.ProjectiveComposition
