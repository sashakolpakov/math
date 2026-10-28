import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ModelSpecifiedSectionCycles
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorModelSections

/-! # Specified Section Tensor Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SpecifiedSectionTensorComparison

noncomputable section

/-! The scalar-extended representatives of specified sections map to
the actual tensor comparison of those sections. Consequently their kernel
completeness is equivalent to bijectivity of that section comparison. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} {R : Type u} [CommRing R]
variable (A : Type u) [AddCommGroup A] [Module R A]
variable (c : R →+* Γ(X, ⊤)) (M N : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (hU : iSup U = ⊤)
variable {D : CochainComplex (ModuleCat.{u} R) ℕ}
variable (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U) [QuasiIsoAt φ 0]

def tensorSpecifiedSectionCycleComparison {κ : Type v}
    (s : κ → (Line.Bundles.structureModule X ⟶ M)) :
    (A ⊗[R] (κ →₀ R)) →ₗ[R] ((D.d 0 1).hom.lTensor A).ker :=
  KernelDimensionCriterion.linearKernelComparison ((Cech.ModelSpecifiedSectionCycles.modelSectionCycleMap c M U hU φ s).lTensor A)
    ((D.d 0 1).hom.lTensor A) (by
      rw [← LinearMap.lTensor_comp, Cech.ModelSpecifiedSectionCycles.modelSectionCycleMap_cycle]
      exact LinearMap.lTensor_zero A)

variable (β : ∀ V : X.Opens, A ⊗[R] ((Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op V)) →ₗ[R]
  (Coefficient.ModulePresheaf.coefficientModulePresheaf c N).obj (op V))
variable (hβ : ∀ (V W : X.Opens) (i : V ⟶ W) (a : A)
    (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op W)),
    β V (a ⊗ₜ[R] (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).map i.op x) =
      (Coefficient.ModulePresheaf.coefficientModulePresheaf c N).map i.op (β W (a ⊗ₜ[R] x)))
variable [QuasiIsoAt (Cech.TensorModelSections.CechTensorComparison.modelMap A c M N U β hβ φ) 0]

theorem tensorSpecifiedSectionCycleComparison_sections {κ : Type v}
    (s : κ → (Line.Bundles.structureModule X ⟶ M)) :
    (Cech.ModelGlobalSections.CechModelSections.equiv c N U hU (Cech.TensorModelSections.CechTensorComparison.modelMap A c M N U β hβ φ)).toLinearMap.comp
        (tensorSpecifiedSectionCycleComparison A c M U hU φ s) =
      (β ⊤).comp ((Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s).lTensor A) := by
  apply TensorProduct.ext'
  intro a x
  let e := Cech.ModelGlobalSections.CechModelSections.equiv c M U hU φ
  let z := Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s x
  have hk : tensorSpecifiedSectionCycleComparison A c M U hU φ s (a ⊗ₜ[R] x) =
      Tensor.DifferentialKernels.tensorDifferentialKernelMap A (D.d 0 1) (a ⊗ₜ[R] e.symm z) := Subtype.ext rfl
  have ht := Cech.TensorModelSections.CechTensorComparison.modelKernel_tensor_section A c M N U β hβ φ hU a (e.symm z)
  change _ = β ⊤ (a ⊗ₜ[R] e (e.symm z)) at ht
  rw [LinearEquiv.apply_symm_apply] at ht
  exact (congrArg (Cech.ModelGlobalSections.CechModelSections.equiv c N U hU
    (Cech.TensorModelSections.CechTensorComparison.modelMap A c M N U β hβ φ)) hk).trans ht

include hβ in
theorem tensorSpecifiedSectionCycleComparison_bijective_iff {κ : Type v}
    (s : κ → (Line.Bundles.structureModule X ⟶ M)) :
    Function.Bijective (tensorSpecifiedSectionCycleComparison A c M U hU φ s) ↔
      Function.Bijective ((β ⊤).comp ((Coefficient.SectionFrameCriterion.coefficientSectionLinearCombination c M s).lTensor A)) := by
  let e := Cech.ModelGlobalSections.CechModelSections.equiv c N U hU (Cech.TensorModelSections.CechTensorComparison.modelMap A c M N U β hβ φ)
  let k := tensorSpecifiedSectionCycleComparison A c M U hU φ s
  have he := tensorSpecifiedSectionCycleComparison_sections A c M N U hU φ β hβ s
  constructor
  · intro h
    rw [← he]
    exact e.bijective.comp h
  · intro h
    rw [← he] at h
    refine ⟨fun x y hxy => h.injective (congrArg e hxy), ?_⟩
    intro y
    obtain ⟨x, hx⟩ := h.surjective (e y)
    exact ⟨x, e.injective hx⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SpecifiedSectionTensorComparison
