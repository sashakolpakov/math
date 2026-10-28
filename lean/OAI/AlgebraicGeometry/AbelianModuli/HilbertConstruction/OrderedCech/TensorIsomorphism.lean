import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.TensorComplex
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Tensor Isomorphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.TensorIsomorphism

noncomputable section

/-! A finite ordered Cech tensor comparison is an isomorphism when each actual intersection-section comparison is an isomorphism. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open scoped TensorProduct
universe u

private theorem pi_lift_map_factor {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {J : Type*} (P : J → C) (Q : J → D)
    [HasProduct P] [HasProduct Q] [HasProduct (fun i => F.obj (P i))]
    (b : ∀ i, F.obj (P i) ⟶ Q i) :
    Pi.lift (fun i => F.map (Pi.π P i) ≫ b i) = piComparison F P ≫ Limits.Pi.map b := by
  apply Pi.hom_ext
  intro i
  rw [Category.assoc, Pi.map_π, ← Category.assoc, piComparison_comp_π]
  exact Pi.lift_comp_π _ i

namespace CechTensorComparison
variable {X : Scheme.{u}} {R : Type u} [CommRing R]
variable (A : Type u) [AddCommGroup A] [Module R A]
variable (c : R →+* Γ(X, ⊤)) (M N : X.Modules)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
variable (β : ∀ V : X.Opens, A ⊗[R] ((Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op V)) →ₗ[R]
  (Coefficient.ModulePresheaf.coefficientModulePresheaf c N).obj (op V))

def factor (V : X.Opens) :
    (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A).obj ((Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op V)) ⟶
      (Coefficient.ModulePresheaf.coefficientModulePresheaf c N).obj (op V) :=
  ModuleCat.ofHom
    (X := (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A).obj ((Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op V)))
    (Y := (Coefficient.ModulePresheaf.coefficientModulePresheaf c N).obj (op V)) (β V)

theorem mapF_factorization (q : ℕ) :
    TensorTerms.CechTensorComparison.mapF A c M N U β q =
      piComparison (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A)
        (fun i : Ordered.SectionCechIndices.OrderedCechIndex ι q => Ordered.CoefficientCechTerms.coefficientCechFactor c M U q i.1) ≫
      Limits.Pi.map (fun i : Ordered.SectionCechIndices.OrderedCechIndex ι q => factor A c M N β (∏ᶜ fun k => U (i.1 k))) :=
  pi_lift_map_factor (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A)
    (fun i : Ordered.SectionCechIndices.OrderedCechIndex ι q => Ordered.CoefficientCechTerms.coefficientCechFactor c M U q i.1)
    (fun i : Ordered.SectionCechIndices.OrderedCechIndex ι q => Ordered.CoefficientCechTerms.coefficientCechFactor c N U q i.1)
    (fun i => factor A c M N β (∏ᶜ fun k => U (i.1 k)))

theorem mapF_isIso [Finite ι] (q : ℕ)
    (h : ∀ i : Ordered.SectionCechIndices.OrderedCechIndex ι q, IsIso (factor A c M N β (∏ᶜ fun k => U (i.1 k)))) :
    IsIso (TensorTerms.CechTensorComparison.mapF A c M N U β q) := by
  have : ∀ i : Ordered.SectionCechIndices.OrderedCechIndex ι q, IsIso (factor A c M N β (∏ᶜ fun k => U (i.1 k))) := h
  have : Finite (Ordered.SectionCechIndices.OrderedCechIndex ι q) :=
    inferInstanceAs (Finite {i : Fin (q + 1) → ι // StrictMono i})
  have hPi : IsIso (piComparison (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A)
      (fun i : Ordered.SectionCechIndices.OrderedCechIndex ι q => Ordered.CoefficientCechTerms.coefficientCechFactor c M U q i.1)) := by
    infer_instance
  have hmap : IsIso (piComparison (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A)
      (fun i : Ordered.SectionCechIndices.OrderedCechIndex ι q => Ordered.CoefficientCechTerms.coefficientCechFactor c M U q i.1) ≫
      Limits.Pi.map (fun i : Ordered.SectionCechIndices.OrderedCechIndex ι q => factor A c M N β (∏ᶜ fun k => U (i.1 k)))) := by
    infer_instance
  exact (congrArg IsIso (mapF_factorization A c M N U β q)).mpr hmap

variable (hβ : ∀ (V W : X.Opens) (i : V ⟶ W) (a : A)
    (x : (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).obj (op W)),
    β V (a ⊗ₜ[R] (Coefficient.ModulePresheaf.coefficientModulePresheaf c M).map i.op x) =
      (Coefficient.ModulePresheaf.coefficientModulePresheaf c N).map i.op (β W (a ⊗ₜ[R] x)))

theorem map_isIso [Finite ι]
    (h : ∀ q (i : Ordered.SectionCechIndices.OrderedCechIndex ι q), IsIso (factor A c M N β (∏ᶜ fun k => U (i.1 k)))) :
    IsIso (TensorComplex.CechTensorComparison.map A c M N U β hβ) := by
  have (q : ℕ) : IsIso ((TensorComplex.CechTensorComparison.map A c M N U β hβ).f q) := mapF_isIso A c M N U β q (h q)
  exact HomologicalComplex.Hom.isIso_of_components _

end CechTensorComparison

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.TensorIsomorphism
