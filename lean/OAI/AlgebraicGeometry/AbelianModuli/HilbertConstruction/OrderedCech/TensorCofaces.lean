import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.TensorTerms

/-! # Tensor Cofaces -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.TensorCofaces.CechTensorComparison

noncomputable section

/-! A tensor comparison compatible with open restriction commutes with every ordered Cech coface. -/
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

theorem coface_comm (q : ℕ) (k : Fin (q + 2)) :
    (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A).map (Ordered.CoefficientCechTerms.orderedCoefficientCechCoface c M U q k) ≫
      TensorTerms.CechTensorComparison.mapF A c M N U β (q + 1) =
    TensorTerms.CechTensorComparison.mapF A c M N U β q ≫ Ordered.CoefficientCechTerms.orderedCoefficientCechCoface c N U q k := by
  apply Pi.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro a x
  have hM := ConcreteCategory.congr_hom (Ordered.CoefficientCechTerms.orderedCoefficientCechCoface_comp_π c M U q k i) x
  have hN := ConcreteCategory.congr_hom (Ordered.CoefficientCechTerms.orderedCoefficientCechCoface_comp_π c N U q k i)
    (TensorTerms.CechTensorComparison.mapF A c M N U β q (a ⊗ₜ[R] x))
  let j := (((FormalCoproduct.mk _ U).mapPower (SimplexCategory.δ k).toOrderHom.toFun).φ i.1)
  have h₁ := TensorTerms.CechTensorComparison.mapF_tmul_π A c M N U β (q + 1) i a (Ordered.CoefficientCechTerms.orderedCoefficientCechCoface c M U q k x)
  have h₂ := congrArg (fun z => β (∏ᶜ fun l => U (i.1 l)) (a ⊗ₜ[R] z)) hM
  have h₃ := hβ _ _ j a
    (Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι q => Ordered.CoefficientCechTerms.coefficientCechFactor c M U q j.1) (i.delete k) x)
  have h₄ := congrArg ((Coefficient.ModulePresheaf.coefficientModulePresheaf c N).map j.op)
    (TensorTerms.CechTensorComparison.mapF_tmul_π A c M N U β q (i.delete k) a x)
  exact h₁.trans (h₂.trans (h₃.trans (h₄.symm.trans hN.symm)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.TensorCofaces.CechTensorComparison
