import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.TensorDifferential

/-! # Tensor Complex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.TensorComplex.CechTensorComparison

noncomputable section

/-! The canonical cochain map induced by a natural tensor comparison on actual sections. -/
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

def map : HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex A (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U) ⟶
    Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c N U :=
  CochainComplex.ofHom (TensorTerms.CechTensorComparison.mapF A c M N U β) (fun q => by
    change TensorTerms.CechTensorComparison.mapF A c M N U β q ≫ (Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c N U).d q (q + 1) =
      (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.tensor A).map ((Ordered.CoefficientCechComplex.orderedCoefficientCechComplex c M U).d q (q + 1)) ≫
        TensorTerms.CechTensorComparison.mapF A c M N U β (q + 1)
    rw [Ordered.CoefficientCechComplex.orderedCoefficientCechComplex_d, Ordered.CoefficientCechComplex.orderedCoefficientCechComplex_d]
    exact (TensorDifferential.CechTensorComparison.differential_comm A c M N U β hβ q).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OrderedCech.TensorComplex.CechTensorComparison
