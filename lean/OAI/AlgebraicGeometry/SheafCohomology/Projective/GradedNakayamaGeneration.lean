import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedNakayama
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedModuleMk

/-! # Graded Nakayama Generation -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedNakayamaGeneration

noncomputable section

/-! Homogeneous generators lift from the augmentation quotient to the whole finite module. -/

open DirectSum
universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ]

theorem gradedPolynomial_eq_top_of_augmentation
    (D : HilbertScheme.Presentations.Finite.GradedPolynomialModules.GradedModules.FiniteGradedPolynomialModule σ R)
    (P : Submodule (MvPolynomial σ R) D.Carrier) (hP : P.IsHomogeneous D.grading)
    (h : P ⊔ GradedNakayama.polynomialAugmentationIdeal (R := R) (σ := σ) • ⊤ = ⊤) : P = ⊤ := by
  let ℚM := GradedModuleMk.GradedModuleQuotient.grading D.grading P
  let : Decomposition ℚM := GradedModuleMk.GradedModuleQuotient.quotientDecomposition D.grading P hP
  have hmap := (P.map_mkQ_eq_top (GradedNakayama.polynomialAugmentationIdeal (R := R) (σ := σ) • ⊤)).mpr h
  rw [Submodule.map_smul'', Submodule.map_top, P.range_mkQ] at hmap
  have : Subsingleton (D.Carrier ⧸ P) := GradedNakayama.gradedPolynomial_nakayama ℚM hmap.symm.le
  apply eq_top_iff.mpr
  intro x _
  exact (Submodule.Quotient.mk_eq_zero P).mp (Subsingleton.elim _ _)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedNakayamaGeneration
