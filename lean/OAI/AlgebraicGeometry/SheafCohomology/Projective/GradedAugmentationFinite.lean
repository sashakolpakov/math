import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedAugmentation

/-! # Graded Augmentation Finite -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedAugmentationFinite

noncomputable section

/-! The augmentation quotient of a finite polynomial module is finite over the base ring. -/

open _root_.MvPolynomial
universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ]

theorem gradedAugmentationQuotient_smul (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R)
    (p : MvPolynomial σ R) (x : (GradedAugmentation.gradedAugmentationQuotient D).Carrier) :
    p • x = (constantCoeff p) • x := by
  let P := GradedNakayama.polynomialAugmentationIdeal (R := R) (σ := σ) •
    (⊤ : Submodule (MvPolynomial σ R) D.Carrier)
  have hp : p - C (constantCoeff p) ∈ GradedNakayama.polynomialAugmentationIdeal (R := R) (σ := σ) := by
    change constantCoeff (p - C (constantCoeff p)) = 0
    rw [map_sub, constantCoeff_C, sub_self]
  rw [← IsScalarTower.algebraMap_smul (MvPolynomial σ R) (constantCoeff p) x]
  apply sub_eq_zero.mp
  rw [← sub_smul]
  obtain ⟨y, rfl⟩ := P.mkQ_surjective x
  change P.mkQ ((p - C (constantCoeff p)) • y) = 0
  exact (Submodule.Quotient.mk_eq_zero P).mpr (Submodule.smul_mem_smul hp (by trivial))

theorem gradedAugmentationQuotient_finite (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R) :
    Module.Finite R (GradedAugmentation.gradedAugmentationQuotient D).Carrier := by
  let f : (GradedAugmentation.gradedAugmentationQuotient D).Carrier →ₛₗ[
      (constantCoeff : MvPolynomial σ R →+* R)] (GradedAugmentation.gradedAugmentationQuotient D).Carrier :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := gradedAugmentationQuotient_smul D }
  exact Module.Finite.of_surjective f Function.surjective_id

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedAugmentationFinite
