import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechTerms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorFunctor

/-! # Tensor Terms -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.TensorTerms.CechTensorComparison

noncomputable section

/-! A sectionwise tensor comparison induces actual maps on ordered Cech terms. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u
variable {X : Scheme.{u}} {R : Type u} [CommRing R]
variable (A : Type u) [AddCommGroup A] [Module R A]
variable (c : R →+* Γ(X, ⊤)) (M N : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
variable (β : ∀ V : X.Opens, A ⊗[R] ((Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op V)) →ₗ[R]
  (Coefficient.ModulePresheaf.coefficientModulePresheaf c N).obj (op V))

def mapF (q : ℕ) :
    (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A).obj (Ordered.CoefficientCechTerms.orderedCoefficientCechObject c M U q) ⟶
      Ordered.CoefficientCechTerms.orderedCoefficientCechObject c N U q :=
  Pi.lift (fun i : Ordered.SectionCechIndices.OrderedCechIndex ι q => ModuleCat.ofHom
    (X := (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A).obj (Ordered.CoefficientCechTerms.orderedCoefficientCechObject c M U q))
    (Y := Ordered.CoefficientCechTerms.coefficientCechFactor c N U q i.1)
    ((β (∏ᶜ fun k => U (i.1 k))).comp
      ((Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι q => Ordered.CoefficientCechTerms.coefficientCechFactor c M U q j.1) i).hom.lTensor A)))

theorem mapF_tmul_π (q : ℕ) (i : Ordered.SectionCechIndices.OrderedCechIndex ι q) (a : A)
    (x : Ordered.CoefficientCechTerms.orderedCoefficientCechObject c M U q) :
    Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι q => Ordered.CoefficientCechTerms.coefficientCechFactor c N U q j.1) i
      (mapF A c M N U β q (a ⊗ₜ[R] x)) =
    β (∏ᶜ fun k => U (i.1 k))
      (a ⊗ₜ[R] Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι q => Ordered.CoefficientCechTerms.coefficientCechFactor c M U q j.1) i x) := by
  let t (j : Ordered.SectionCechIndices.OrderedCechIndex ι q) :
      (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A).obj (Ordered.CoefficientCechTerms.orderedCoefficientCechObject c M U q) ⟶
        Ordered.CoefficientCechTerms.coefficientCechFactor c N U q j.1 :=
    ModuleCat.ofHom
      (X := (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A).obj (Ordered.CoefficientCechTerms.orderedCoefficientCechObject c M U q))
      (Y := Ordered.CoefficientCechTerms.coefficientCechFactor c N U q j.1)
      ((β (∏ᶜ fun k => U (j.1 k))).comp
        ((Pi.π (fun l : Ordered.SectionCechIndices.OrderedCechIndex ι q => Ordered.CoefficientCechTerms.coefficientCechFactor c M U q l.1) j).hom.lTensor A))
  have h : mapF A c M N U β q ≫
      Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι q => Ordered.CoefficientCechTerms.coefficientCechFactor c N U q j.1) i = t i :=
    Pi.lift_comp_π t i
  exact ConcreteCategory.congr_hom h (a ⊗ₜ[R] x)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.TensorTerms.CechTensorComparison
