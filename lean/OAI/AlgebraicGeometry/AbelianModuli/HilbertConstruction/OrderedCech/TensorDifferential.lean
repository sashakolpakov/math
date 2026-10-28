import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.TensorCofaces
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ordered.CoefficientCechComplex
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Tensor Differential -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.TensorDifferential

noncomputable section

/-! Tensor comparison commutes with the full alternating Cech differential. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits
section

private theorem functor_weighted_sum_square
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {P Q : C} {P' Q' : D}
    (a : F.obj P ⟶ P') (b : F.obj Q ⟶ Q') {J : Type*} [Fintype J]
    (z : J → ℤ) (f : J → (P ⟶ Q)) (g : J → (P' ⟶ Q'))
    (h : ∀ j, F.map (f j) ≫ b = a ≫ g j) :
    F.map (∑ j, z j • f j) ≫ b = a ≫ ∑ j, z j • g j := by
  rw [F.map_sum, Preadditive.sum_comp, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [F.map_zsmul, Preadditive.zsmul_comp, Preadditive.comp_zsmul, h j]

end

namespace CechTensorComparison
open _root_.AlgebraicGeometry Opposite
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

theorem differential_comm (q : ℕ) :
    (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A).map (Ordered.CoefficientCechComplex.orderedCoefficientCechDifferential c M U q) ≫
      TensorTerms.CechTensorComparison.mapF A c M N U β (q + 1) =
    TensorTerms.CechTensorComparison.mapF A c M N U β q ≫ Ordered.CoefficientCechComplex.orderedCoefficientCechDifferential c N U q :=
  functor_weighted_sum_square (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A)
    (TensorTerms.CechTensorComparison.mapF A c M N U β q) (TensorTerms.CechTensorComparison.mapF A c M N U β (q + 1))
    (fun k : Fin (q + 2) => (-1 : ℤ) ^ k.val)
    (Ordered.CoefficientCechTerms.orderedCoefficientCechCoface c M U q) (Ordered.CoefficientCechTerms.orderedCoefficientCechCoface c N U q)
    (TensorCofaces.CechTensorComparison.coface_comm A c M N U β hβ q)

end CechTensorComparison

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.TensorDifferential
