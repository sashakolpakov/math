import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.ModelGlobalSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorSectionNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.DifferentialKernels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.AugmentationInjectivity

/-! # Tensor Model Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorModelSections.CechTensorComparison

noncomputable section

/-! The tensor model map sends pure tensors of actual model sections to their prescribed sectionwise tensor images. -/
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

def modelMap : HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex A D ⟶ Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c N U :=
  HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map A φ ≫ OrderedCech.TensorComplex.CechTensorComparison.map A c M N U β hβ

variable (hU : iSup U = ⊤) [QuasiIsoAt φ 0]
variable [QuasiIsoAt (modelMap A c M N U β hβ φ) 0]

theorem modelKernel_tensor_section (a : A) (m : (D.d 0 1).hom.ker) :
    ModelGlobalSections.CechModelSections.equiv c N U hU (modelMap A c M N U β hβ φ)
      (Tensor.DifferentialKernels.tensorDifferentialKernelMap A (D.d 0 1) (a ⊗ₜ[R] m)) =
    β ⊤ (a ⊗ₜ[R] ModelGlobalSections.CechModelSections.equiv c M U hU φ m) := by
  apply OrderedCech.AugmentationInjectivity.orderedCechSectionToCycles_injective c N U (fun x => by
    have hx : x ∈ iSup U := by rw [hU]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx)
  apply Subtype.ext
  have ht := ModelGlobalSections.CechModelSections.coordinate c N U hU (modelMap A c M N U β hβ φ)
    (Tensor.DifferentialKernels.tensorDifferentialKernelMap A (D.d 0 1) (a ⊗ₜ[R] m))
  have hs := congrArg (fun z => OrderedCech.TensorTerms.CechTensorComparison.mapF A c M N U β 0 (a ⊗ₜ[R] z))
    (ModelGlobalSections.CechModelSections.coordinate c M U hU φ m)
  have hn := ConcreteCategory.congr_hom (TensorSectionNormalization.CechTensorComparison.sectionMap_comm A c M N U β hβ 0)
    (a ⊗ₜ[R] ModelGlobalSections.CechModelSections.equiv c M U hU φ m)
  exact ht.symm.trans (hs.trans hn)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorModelSections.CechTensorComparison
