import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.TensorComplex
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.CochainBicomplex

/-! # Tensor Comparison Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorComparisonNaturality

noncomputable section

/-! A sectionwise tensor comparison is natural under compatible maps of the tensor factor and coefficient sheaf. The resulting equality is an equality of actual Cech cochain maps. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

theorem orderedCoefficientCechObjectFunctor_map_π
    (c : R →+* Γ(X, ⊤)) {M N : X.Modules} (a : M ⟶ N)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (q : ℕ) (i : Ordered.SectionCechIndices.OrderedCechIndex ι q) :
    (Ordered.CoefficientCechFunctor.orderedCoefficientCechObjectFunctor c U q).map a ≫
        Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι q => Ordered.CoefficientCechTerms.coefficientCechFactor c N U q j.1) i =
      Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι q => Ordered.CoefficientCechTerms.coefficientCechFactor c M U q j.1) i ≫
        ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).map a).app (op (∏ᶜ fun k => U (i.1 k))) := by
  let p (j : Ordered.SectionCechIndices.OrderedCechIndex ι q) :
      Ordered.CoefficientCechTerms.coefficientCechFactor c M U q j.1 ⟶ Ordered.CoefficientCechTerms.coefficientCechFactor c N U q j.1 :=
    ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).map a).app (op (∏ᶜ fun k => U (j.1 k)))
  change CategoryTheory.Limits.Pi.map p ≫ _ = _
  exact Pi.map_π p i

namespace CechTensorComparison
variable (A B : Type u) [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
variable (c : R →+* Γ(X, ⊤)) (M N P : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
variable (a : A →ₗ[R] B) (e : N ⟶ P)
variable (β : ∀ V : X.Opens, A ⊗[R] ((Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op V)) →ₗ[R]
  (Coefficient.ModulePresheaf.coefficientModulePresheaf c N).obj (op V))
variable (γ : ∀ V : X.Opens, B ⊗[R] ((Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op V)) →ₗ[R]
  (Coefficient.ModulePresheaf.coefficientModulePresheaf c P).obj (op V))
variable (hcompat : ∀ (V : X.Opens) (x : A)
  (m : (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op V)),
  ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).map e).app (op V) (β V (x ⊗ₜ[R] m)) =
    γ V (a x ⊗ₜ[R] m))

include hcompat in
theorem mapF_naturality (q : ℕ) :
    OrderedCech.TensorTerms.CechTensorComparison.mapF A c M N U β q ≫ (Ordered.CoefficientCechFunctor.orderedCoefficientCechObjectFunctor c U q).map e =
      ModuleCat.ofHom (a.rTensor (Ordered.CoefficientCechTerms.orderedCoefficientCechObject c M U q)) ≫
        OrderedCech.TensorTerms.CechTensorComparison.mapF B c M P U γ q := by
  let t : Ordered.CoefficientCechTerms.orderedCoefficientCechObject c N U q ⟶ Ordered.CoefficientCechTerms.orderedCoefficientCechObject c P U q :=
    (Ordered.CoefficientCechFunctor.orderedCoefficientCechObjectFunctor c U q).map e
  change OrderedCech.TensorTerms.CechTensorComparison.mapF A c M N U β q ≫ t = _
  apply Pi.hom_ext
  intro i
  change Ordered.SectionCechIndices.OrderedCechIndex ι q at i
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x m
  have ht := ConcreteCategory.congr_hom
    (orderedCoefficientCechObjectFunctor_map_π c e U q i)
    (OrderedCech.TensorTerms.CechTensorComparison.mapF A c M N U β q (x ⊗ₜ[R] m))
  change Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι q => Ordered.CoefficientCechTerms.coefficientCechFactor c P U q j.1) i
      (t (OrderedCech.TensorTerms.CechTensorComparison.mapF A c M N U β q (x ⊗ₜ[R] m))) =
    Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι q => Ordered.CoefficientCechTerms.coefficientCechFactor c P U q j.1) i
      (OrderedCech.TensorTerms.CechTensorComparison.mapF B c M P U γ q (a x ⊗ₜ[R] m))
  change Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι q => Ordered.CoefficientCechTerms.coefficientCechFactor c P U q j.1) i
      (t (OrderedCech.TensorTerms.CechTensorComparison.mapF A c M N U β q (x ⊗ₜ[R] m))) =
    ((Coefficient.ModulePresheafFunctor.coefficientModulePresheafFunctor c).map e).app (op (∏ᶜ fun k => U (i.1 k)))
      (Pi.π (fun j : Ordered.SectionCechIndices.OrderedCechIndex ι q => Ordered.CoefficientCechTerms.coefficientCechFactor c N U q j.1) i
        (OrderedCech.TensorTerms.CechTensorComparison.mapF A c M N U β q (x ⊗ₜ[R] m))) at ht
  rw [ht]
  rw [OrderedCech.TensorTerms.CechTensorComparison.mapF_tmul_π, OrderedCech.TensorTerms.CechTensorComparison.mapF_tmul_π]
  exact hcompat _ x _

include hcompat in
theorem map_naturality
    (hβ : ∀ (V W : X.Opens) (i : V ⟶ W) (x : A)
      (m : (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op W)),
      β V (x ⊗ₜ[R] (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).map i.op m) =
        (Coefficient.ModulePresheaf.coefficientModulePresheaf c N).map i.op (β W (x ⊗ₜ[R] m)))
    (hγ : ∀ (V W : X.Opens) (i : V ⟶ W) (x : B)
      (m : (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op W)),
      γ V (x ⊗ₜ[R] (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).map i.op m) =
        (Coefficient.ModulePresheaf.coefficientModulePresheaf c P).map i.op (γ W (x ⊗ₜ[R] m))) :
    OrderedCech.TensorComplex.CechTensorComparison.map A c M N U β hβ ≫ (Ordered.CoefficientCechFunctor.orderedCoefficientCechComplexFunctor c U).map e =
      Tensor.CochainBicomplex.tensorCochainMap (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U) (ModuleCat.ofHom a) ≫
        OrderedCech.TensorComplex.CechTensorComparison.map B c M P U γ hγ := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact mapF_naturality A B c M N P U a e β γ hcompat q

end CechTensorComparison

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.TensorComparisonNaturality
