import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.AugmentationMap
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.TermTensorInclusion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.Singleton
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Section Map -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.SectionMap.ProjectiveCech

noncomputable section

/-! The homogeneous section map into actual localized Čech cochains and its tensor injectivity. -/

open _root_.MvPolynomial DirectSum

universe u v w

variable {σ : Type v} [Fintype σ] [LinearOrder σ]
variable (R : Type u) [CommRing R]
variable (M : Type (max u v)) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]
variable (ℳ : ℤ → Submodule R M)
  [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]

def moduleDegreeSectionMap (d : ℤ) : ℳ d →ₗ[R] ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M :=
  (ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := σ) R M ℳ d 1).subtype.comp
    ((ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d 0).comp
      (AugmentationMap.ProjectiveCech.moduleAugmentationToTerm (σ := σ) R M ℳ d))

omit [Fintype σ] in
theorem moduleCechValue_augmentation (m : M) (s t : Finset σ) (h : t ⊆ s) (ht : t.card = 0) :
    ModuleCech.Square.ProjectiveCech.moduleCechValue R M (EventualIrrelevantTorsion.ProjectiveCech.moduleAugmentationCochain (σ := σ) R M m) s t h =
      Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) 0 m := by
  change Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M h (if t.card = 0 then _ else _) = _
  rw [ite_eq_left ht, Presentations.Module.ChartCompatibility.ProjectiveCech.moduleChartRestriction_fraction, pow_zero, one_smul]

omit [Fintype σ] in
theorem moduleDegreeSectionMap_singleton (d : ℤ) (m : ℳ d) (i : σ) :
    moduleDegreeSectionMap (σ := σ) R M ℳ d m {i} =
      Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R {i}) 0 m.val := by
  change ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M (EventualIrrelevantTorsion.ProjectiveCech.moduleAugmentationCochain (σ := σ) R M m.val) {i} = _
  rw [Singleton.ProjectiveCech.moduleCechDifferential_singleton]
  have hsign : Signs.ProjectiveCech.alternatingSign R {i} i = 1 := by
    have he : ({i} : Finset σ).filter (fun j => j < i) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro j hj
      have hj' := Finset.mem_singleton.mp hj
      subst j
      exact lt_irrefl i
    simp only [Signs.ProjectiveCech.alternatingSign, he, Finset.card_empty, pow_zero]
  rw [hsign, one_smul]
  exact moduleCechValue_augmentation R M m.val {i} (({i} : Finset σ).erase i) (Finset.erase_subset i {i})
    (by simp only [Finset.erase_singleton, Finset.card_empty])

omit [Fintype σ] in
theorem moduleDegreeSectionMap_proj (d : ℤ) (s : Finset σ) :
    (LinearMap.proj s).comp (moduleDegreeSectionMap (σ := σ) R M ℳ d) =
      if s.card = 1 then (Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) 0).comp (ℳ d).subtype
      else 0 := by
  apply LinearMap.ext
  intro m
  by_cases hs : s.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hs
    simpa only [ite_eq_left (Finset.card_singleton i), LinearMap.comp_apply, LinearMap.proj_apply,
      Submodule.subtype_apply] using moduleDegreeSectionMap_singleton R M ℳ d m i
  · rw [ite_eq_right hs]
    exact (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := σ) R M ℳ d 0
      (AugmentationMap.ProjectiveCech.moduleAugmentationToTerm (σ := σ) R M ℳ d m)).property.2 s hs

theorem moduleDegreeSectionMap_tensor_coordinate (d : ℤ)
    (S : Type w) [AddCommGroup S] [Module R S]
    (x : TensorProduct R S (ℳ d)) (s : Finset σ) :
    TensorProduct.piRight R R S (fun t : Finset σ => Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M t)
      ((moduleDegreeSectionMap (σ := σ) R M ℳ d).lTensor S x) s =
      (((LinearMap.proj s).comp (moduleDegreeSectionMap (σ := σ) R M ℳ d)).lTensor S) x := by
  induction x using TensorProduct.inductionOn with
  | tmul r m => rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem moduleDegreeSectionMap_eventual_lTensor_injective [Nonempty σ] [IsNoetherianRing R]
    [Decomposition ℳ] [Module.Finite (MvPolynomial σ R) M]
    (hflat : ∀ s : Finset σ, s.Nonempty → Module.Flat R (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s 0)) :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d →
      ∀ (S : Type w) [AddCommGroup S] [Module R S],
        Function.Injective ((moduleDegreeSectionMap (σ := σ) R M ℳ d).lTensor S) := by
  obtain ⟨B, hB⟩ := TensorAugmentation.ProjectiveCech.moduleCech_eventual_lTensor_injective (σ := σ) R M ℳ hflat
  refine ⟨B, fun d hd S _ _ => ?_⟩
  rw [moduleDegreeSectionMap, LinearMap.lTensor_comp, LinearMap.lTensor_comp]
  exact (TermTensorInclusion.ProjectiveCech.moduleCechTermSubtype_lTensor_injective R M ℳ d 1 S).comp
    ((hB d hd S).comp (AugmentationMap.ProjectiveCech.moduleAugmentationToTerm_lTensor_injective R M ℳ d S))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.SectionMap.ProjectiveCech
