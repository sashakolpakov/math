import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPieceFiniteness
import OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedCyclicSubmodule

/-! # Graded Polynomial Constant Component -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPolynomialConstantComponent

noncomputable section

/-! Degree zero in the integer polynomial grading is the actual constant coefficient. -/

open DirectSum _root_.MvPolynomial
universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ]

theorem polynomialIntegerGrading_decompose_zero (p : MvPolynomial σ R) :
    (decompose (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading R) p 0).val = C (constantCoeff p) := by
  classical
  change (MvPolynomial.decompose' R (fun _ : σ => (1 : ℤ)) p 0).val = C (constantCoeff p)
  rw [MvPolynomial.decompose'_apply]
  apply MvPolynomial.ext
  intro a
  rw [coeff_weightedHomogeneousComponent, coeff_C]
  by_cases h : a = 0
  · simp [h]
    rfl
  · have hw : Finsupp.weight (fun _ : σ => (1 : ℤ)) a ≠ 0 := by
      rw [HilbertScheme.Presentations.IntegerPolynomialGrading.GradedModules.integerWeight_eq_degree]
      exact_mod_cast (mt (Finsupp.degree_eq_zero_iff a).mp h)
    simp [hw, Ne.symm h]

theorem homogeneous_smul_constant_component
    {M : Type u} [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
    [IsScalarTower R (MvPolynomial σ R) M]
    (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
    [SetLike.GradedSMul (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
    {d : ℤ} {x : M} (hx : x ∈ ℳ d) (p : MvPolynomial σ R) :
    (decompose ℳ (p • x) d).val = (constantCoeff p) • x := by
  rw [GradedCyclicSubmodule.homogeneous_smul_component (HilbertScheme.Presentations.WeightedFreeModules.GradedModules.polynomialIntegerGrading R) ℳ hx, sub_self,
    polynomialIntegerGrading_decompose_zero]
  exact IsScalarTower.algebraMap_smul (MvPolynomial σ R) (constantCoeff p) x

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GradedPolynomialConstantComponent
