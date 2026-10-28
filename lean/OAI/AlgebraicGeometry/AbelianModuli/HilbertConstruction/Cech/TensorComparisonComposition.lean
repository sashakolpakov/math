import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.TensorComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DoubleTensorCochainMap

/-! # Tensor Comparison Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorComparisonComposition.CechTensorComparison

noncomputable section

/-! Composition of actual section tensor pairings induces composition of their actual ordered Cech cochain maps. The specified combination of tensor factors is retained explicitly. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u
variable {X : Scheme.{u}} {R : Type u} [CommRing R]
variable (A B C : Type u) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
variable [AddCommGroup C] [Module R C]
variable (c : R →+* Γ(X, ⊤)) (M N P : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
variable (μ : B ⊗[R] A →ₗ[R] C)
variable (β : ∀ V : X.Opens, A ⊗[R] ((Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op V)) →ₗ[R]
  (Coefficient.ModulePresheaf.coefficientModulePresheaf c N).obj (op V))
variable (γ : ∀ V : X.Opens, B ⊗[R] ((Coefficient.ModulePresheaf.coefficientModulePresheaf c N).obj (op V)) →ₗ[R]
  (Coefficient.ModulePresheaf.coefficientModulePresheaf c P).obj (op V))
variable (δ : ∀ V : X.Opens, C ⊗[R] ((Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op V)) →ₗ[R]
  (Coefficient.ModulePresheaf.coefficientModulePresheaf c P).obj (op V))
variable (hcompat : ∀ (V : X.Opens) (b : B) (a : A)
  (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op V)),
  γ V (b ⊗ₜ[R] β V (a ⊗ₜ[R] x)) = δ V (μ (b ⊗ₜ[R] a) ⊗ₜ[R] x))

include hcompat in
theorem mapF_comp_tensor (n : ℕ) :
    (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor B).map (OrderedCech.TensorTerms.CechTensorComparison.mapF A c M N U β n) ≫ OrderedCech.TensorTerms.CechTensorComparison.mapF B c N P U γ n =
      ModuleCat.ofHom (DoubleTensorCochainMap.doubleTensorCollapse μ (Ordered.CoefficientCechTerms.orderedCoefficientCechObject c M U n)) ≫
        OrderedCech.TensorTerms.CechTensorComparison.mapF C c M P U δ n := by
  apply Pi.hom_ext
  intro i
  change Ordered.SectionCechIndices.OrderedCechIndex ι n at i
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro b z
  change Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι n => Ordered.CoefficientCechTerms.coefficientCechFactor c P U n j.1) i
      (OrderedCech.TensorTerms.CechTensorComparison.mapF B c N P U γ n (b ⊗ₜ[R] OrderedCech.TensorTerms.CechTensorComparison.mapF A c M N U β n z)) =
    Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι n => Ordered.CoefficientCechTerms.coefficientCechFactor c P U n j.1) i
      (OrderedCech.TensorTerms.CechTensorComparison.mapF C c M P U δ n (DoubleTensorCochainMap.doubleTensorCollapse μ (Ordered.CoefficientCechTerms.orderedCoefficientCechObject c M U n) (b ⊗ₜ[R] z)))
  let OM := Ordered.CoefficientCechTerms.orderedCoefficientCechObject c M U n
  let ON := Ordered.CoefficientCechTerms.orderedCoefficientCechObject c N U n
  let OP := Ordered.CoefficientCechTerms.orderedCoefficientCechObject c P U n
  let π : OP →ₗ[R] Ordered.CoefficientCechTerms.coefficientCechFactor c P U n i.1 :=
    (Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι n => Ordered.CoefficientCechTerms.coefficientCechFactor c P U n j.1) i).hom
  let fA : A ⊗[R] OM →ₗ[R] ON := (OrderedCech.TensorTerms.CechTensorComparison.mapF A c M N U β n).hom
  let fB : B ⊗[R] ON →ₗ[R] OP := (OrderedCech.TensorTerms.CechTensorComparison.mapF B c N P U γ n).hom
  let fC : C ⊗[R] OM →ₗ[R] OP := (OrderedCech.TensorTerms.CechTensorComparison.mapF C c M P U δ n).hom
  let l := π.comp (fB.comp ((TensorProduct.mk R B ON b).comp fA))
  let r := π.comp (fC.comp ((DoubleTensorCochainMap.doubleTensorCollapse μ OM).comp
    (TensorProduct.mk R B (A ⊗[R] OM) b)))
  have he : l = r := by
    apply TensorProduct.ext'
    intro a x
    change Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι n => Ordered.CoefficientCechTerms.coefficientCechFactor c P U n j.1) i
        (OrderedCech.TensorTerms.CechTensorComparison.mapF B c N P U γ n (b ⊗ₜ[R] OrderedCech.TensorTerms.CechTensorComparison.mapF A c M N U β n (a ⊗ₜ[R] x))) =
      Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι n => Ordered.CoefficientCechTerms.coefficientCechFactor c P U n j.1) i
        (OrderedCech.TensorTerms.CechTensorComparison.mapF C c M P U δ n (μ (b ⊗ₜ[R] a) ⊗ₜ[R] x))
    let V := ∏ᶜ fun k => U (i.1 k)
    let xi : (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op V) :=
      Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι n => Ordered.CoefficientCechTerms.coefficientCechFactor c M U n j.1) i x
    have hA := OrderedCech.TensorTerms.CechTensorComparison.mapF_tmul_π A c M N U β n i a x
    have hB := OrderedCech.TensorTerms.CechTensorComparison.mapF_tmul_π B c N P U γ n i b (OrderedCech.TensorTerms.CechTensorComparison.mapF A c M N U β n (a ⊗ₜ[R] x))
    have hC := OrderedCech.TensorTerms.CechTensorComparison.mapF_tmul_π C c M P U δ n i (μ (b ⊗ₜ[R] a)) x
    exact hB.trans ((congrArg (fun v : (Coefficient.ModulePresheaf.coefficientModulePresheaf c N).obj (op V) =>
      γ V (b ⊗ₜ[R] v)) hA).trans ((hcompat V b a xi).trans hC.symm))
  exact LinearMap.congr_fun he z

include hcompat in
theorem map_comp_tensor
    (hβ : ∀ (V W : X.Opens) (i : V ⟶ W) (a : A)
      (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op W)),
      β V (a ⊗ₜ[R] (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).map i.op x) =
        (Coefficient.ModulePresheaf.coefficientModulePresheaf c N).map i.op (β W (a ⊗ₜ[R] x)))
    (hγ : ∀ (V W : X.Opens) (i : V ⟶ W) (b : B)
      (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf c N).obj (op W)),
      γ V (b ⊗ₜ[R] (Coefficient.ModulePresheaf.coefficientModulePresheaf c N).map i.op x) =
        (Coefficient.ModulePresheaf.coefficientModulePresheaf c P).map i.op (γ W (b ⊗ₜ[R] x)))
    (hδ : ∀ (V W : X.Opens) (i : V ⟶ W) (a : C)
      (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op W)),
      δ V (a ⊗ₜ[R] (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).map i.op x) =
        (Coefficient.ModulePresheaf.coefficientModulePresheaf c P).map i.op (δ W (a ⊗ₜ[R] x))) :
    HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B (OrderedCech.TensorComplex.CechTensorComparison.map A c M N U β hβ) ≫ OrderedCech.TensorComplex.CechTensorComparison.map B c N P U γ hγ =
      DoubleTensorCochainMap.doubleTensorCochainMap μ (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U) ≫ OrderedCech.TensorComplex.CechTensorComparison.map C c M P U δ hδ := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact mapF_comp_tensor A B C c M N P U μ β γ δ hcompat n

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorComparisonComposition.CechTensorComparison
