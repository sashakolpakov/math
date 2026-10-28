import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorModelSections

/-! # Tensor Sections Surjectivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorSectionsSurjectivity.CechTensorComparison

noncomputable section

/-! Surjectivity of the canonical kernel tensor map implies surjectivity of the actual section tensor comparison. -/
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

include hU hφ hψ

theorem sections_surjective_of_kernel_range
    (h : ((D.d 0 1).hom.lTensor A).ker ≤ ((D.d 0 1).hom.ker.subtype.lTensor A).range) :
    Function.Surjective (β ⊤) := by
  let eM := ModelGlobalSections.CechModelSections.equiv c M U hU φ
  let eN := ModelGlobalSections.CechModelSections.equiv c N U hU (TensorModelSections.CechTensorComparison.modelMap A c M N U β hβ φ)
  have he : (β ⊤).comp (eM.toLinearMap.lTensor A) =
      eN.toLinearMap.comp (Tensor.DifferentialKernels.tensorDifferentialKernelMap A (D.d 0 1)) := by
    apply TensorProduct.ext'
    intro a m
    exact (TensorModelSections.CechTensorComparison.modelKernel_tensor_section A c M N U β hβ φ hU a m).symm
  intro y
  obtain ⟨w, hw⟩ := Tensor.DifferentialKernels.tensorDifferentialKernelMap_surjective A (D.d 0 1) h (eN.symm y)
  refine ⟨eM.toLinearMap.lTensor A w, ?_⟩
  exact (congrArg (fun k => k w) he).trans
    ((congrArg eN hw).trans (eN.apply_symm_apply y))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorSectionsSurjectivity.CechTensorComparison
