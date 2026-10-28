import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EventualIrrelevantTorsion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.TensorInclusions

/-! # Augmentation Map -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.AugmentationMap.ProjectiveCech

noncomputable section

/-! Linear augmentation maps from homogeneous modules to projective Čech terms. -/

open _root_.MvPolynomial DirectSum

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.TensorInclusions.GradedModules

universe u v w

variable {σ : Type v} [Fintype σ] [LinearOrder σ]
variable (R : Type u) [CommRing R]
variable (M : Type (max u v)) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M)

def moduleAugmentationToTerm (d : ℤ) : ℳ d →ₗ[R] ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d 0 where
  toFun m := ⟨EventualIrrelevantTorsion.ProjectiveCech.moduleAugmentationCochain (σ := σ) R M m.val,
    EventualIrrelevantTorsion.ProjectiveCech.moduleAugmentationCochain_homogeneous R M ℳ d m.val m.property,
    EventualIrrelevantTorsion.ProjectiveCech.moduleAugmentationCochain_card R M m.val⟩
  map_add' x y := by
    apply Subtype.ext
    funext s
    by_cases hs : s.card = 0
    · simp only [EventualIrrelevantTorsion.ProjectiveCech.moduleAugmentationCochain, ite_eq_left hs, Submodule.coe_add, Pi.add_apply, map_add]
    · simp only [EventualIrrelevantTorsion.ProjectiveCech.moduleAugmentationCochain, ite_eq_right hs, Submodule.coe_add, Pi.add_apply, add_zero]
  map_smul' r x := by
    apply Subtype.ext
    funext s
    by_cases hs : s.card = 0
    · simp only [EventualIrrelevantTorsion.ProjectiveCech.moduleAugmentationCochain, ite_eq_left hs, Submodule.coe_smul, Pi.smul_apply, map_smul,
        RingHom.id_apply]
    · simp only [EventualIrrelevantTorsion.ProjectiveCech.moduleAugmentationCochain, ite_eq_right hs, Submodule.coe_smul, Pi.smul_apply, smul_zero,
        RingHom.id_apply]

variable [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]

omit [Fintype σ] [LinearOrder σ] in
theorem moduleAugmentationToTerm_equiv (d : ℤ) :
    moduleAugmentationToTerm (σ := σ) R M ℳ d =
      (AugmentationDegree.ProjectiveCech.moduleCechAugmentationEquiv (σ := σ) R M ℳ d).symm.toLinearMap := by
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  funext s
  by_cases hs : s.card = 0
  · have he : s = ∅ := Finset.card_eq_zero.mp hs
    subst s
    rfl
  · change (if s.card = 0 then _ else _) = _
    rw [ite_eq_right hs]
    exact (((AugmentationDegree.ProjectiveCech.moduleCechAugmentationEquiv (σ := σ) R M ℳ d).symm m).property.2 s hs).symm

omit [Fintype σ] [LinearOrder σ] in
theorem moduleAugmentationToTerm_lTensor_injective (d : ℤ)
    (S : Type w) [AddCommGroup S] [Module R S] :
    Function.Injective ((moduleAugmentationToTerm (σ := σ) R M ℳ d).lTensor S) := by
  rw [moduleAugmentationToTerm_equiv]
  exact ((AugmentationDegree.ProjectiveCech.moduleCechAugmentationEquiv (σ := σ) R M ℳ d).symm.lTensor S).injective

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.AugmentationMap.ProjectiveCech
