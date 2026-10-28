import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorModelSections

/-! # Tensor Sections Injectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorSectionsInjectivity.CechTensorComparison

noncomputable section

/-! Injectivity of the original kernel inclusion after tensoring implies injectivity of the actual section tensor comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u
variable {X : Scheme.{u}} {R : Type u} [CommRing R]
variable (A : Type u) [AddCommGroup A] [Module R A]
variable (c : R →+* Γ(X, ⊤)) (M N : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
variable (β : ∀ V : X.Opens, A ⊗[R] ((Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op V)) →ₗ[R]
  (Coefficient.ModulePresheaf.coefficientModulePresheaf c N).obj (op V))
variable (hβ : ∀ (V W : X.Opens) (i : V ⟶ W) (a : A)
    (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op W)),
    β V (a ⊗ₜ[R] (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).map i.op x) =
      (Coefficient.ModulePresheaf.coefficientModulePresheaf c N).map i.op (β W (a ⊗ₜ[R] x)))
variable {D : CochainComplex (ModuleCat.{u} R) ℕ}
variable (φ : D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U)
variable (hU : iSup U = ⊤) [hφ : QuasiIsoAt φ 0]
variable [hψ : QuasiIsoAt (TensorModelSections.CechTensorComparison.modelMap A c M N U β hβ φ) 0]

include hU hφ hψ in
theorem sections_injective_of_kernel_tensor
    (h : Function.Injective ((D.d 0 1).hom.ker.subtype.lTensor A)) :
    Function.Injective (β ⊤) := by
  let eM := ModelGlobalSections.CechModelSections.equiv c M U hU φ
  let eN := ModelGlobalSections.CechModelSections.equiv c N U hU (TensorModelSections.CechTensorComparison.modelMap A c M N U β hβ φ)
  let eT := TensorProduct.congr (LinearEquiv.refl R A) eM
  have he : (β ⊤).comp (eM.toLinearMap.lTensor A) =
      eN.toLinearMap.comp (Tensor.DifferentialKernels.tensorDifferentialKernelMap A (D.d 0 1)) := by
    apply TensorProduct.ext'
    intro a m
    exact (TensorModelSections.CechTensorComparison.modelKernel_tensor_section A c M N U β hβ φ hU a m).symm
  have hk : Function.Injective (Tensor.DifferentialKernels.tensorDifferentialKernelMap A (D.d 0 1)) := by
    intro x y hxy
    exact h (congrArg Subtype.val hxy)
  intro x y hxy
  obtain ⟨x', rfl⟩ := eT.surjective x
  obtain ⟨y', rfl⟩ := eT.surjective y
  have hx := congrArg (fun k => k x') he
  have hy := congrArg (fun k => k y') he
  have hz : eN (Tensor.DifferentialKernels.tensorDifferentialKernelMap A (D.d 0 1) x') =
      eN (Tensor.DifferentialKernels.tensorDifferentialKernelMap A (D.d 0 1) y') := hx.symm.trans (hxy.trans hy)
  exact congrArg eT (hk (eN.injective hz))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorSectionsInjectivity.CechTensorComparison
