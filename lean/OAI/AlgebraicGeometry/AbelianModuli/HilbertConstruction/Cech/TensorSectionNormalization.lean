import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.TensorIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.Augmentation

/-! # Tensor Section Normalization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorSectionNormalization.CechTensorComparison

noncomputable section

/-! The Cech tensor map sends the cochain of a global section to the cochain of its actual sectionwise tensor image. -/
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

include hβ

theorem sectionMap_comm (q : ℕ) :
    (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A).map (OrderedCech.Augmentation.orderedCechSectionMap c M U q) ≫ OrderedCech.TensorTerms.CechTensorComparison.mapF A c M N U β q =
      OrderedCech.TensorIsomorphism.CechTensorComparison.factor A c M N β ⊤ ≫ OrderedCech.Augmentation.orderedCechSectionMap c N U q := by
  apply Pi.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a s
  have h₁ := OrderedCech.TensorTerms.CechTensorComparison.mapF_tmul_π A c M N U β q i a (OrderedCech.Augmentation.orderedCechSectionMap c M U q s)
  have h₂ := congrArg (fun z => β (∏ᶜ fun k => U (i.1 k)) (a ⊗ₜ[R] z))
    (ConcreteCategory.congr_hom (OrderedCech.Augmentation.orderedCechSectionMap_comp_π c M U q i) s)
  have h₃ := hβ (∏ᶜ fun k => U (i.1 k)) ⊤ (homOfLE le_top) a s
  have h₄ := ConcreteCategory.congr_hom (OrderedCech.Augmentation.orderedCechSectionMap_comp_π c N U q i) (β ⊤ (a ⊗ₜ[R] s))
  exact h₁.trans (h₂.trans (h₃.trans h₄.symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorSectionNormalization.CechTensorComparison
