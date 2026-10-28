import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.TensorFunctor
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! # Double Tensor Cochain Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DoubleTensorCochainMap

noncomputable section

/-! A specified bilinear combination of two tensor factors induces a natural map on the actual double-tensor cochain complex. -/
open _root_.CategoryTheory
open scoped TensorProduct
universe u
variable {R A B C : Type u} [CommRing R]
variable [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
variable [AddCommGroup C] [Module R C]
variable (μ : B ⊗[R] A →ₗ[R] C)

def doubleTensorCollapse (M : Type u) [AddCommGroup M] [Module R M] :
    B ⊗[R] (A ⊗[R] M) →ₗ[R] C ⊗[R] M :=
  (μ.rTensor M).comp (TensorProduct.assoc R B A M).symm.toLinearMap

theorem doubleTensorCollapse_tmul (M : Type u) [AddCommGroup M] [Module R M]
    (b : B) (a : A) (m : M) :
    doubleTensorCollapse μ M (b ⊗ₜ[R] (a ⊗ₜ[R] m)) = μ (b ⊗ₜ[R] a) ⊗ₜ[R] m := rfl

theorem doubleTensorCollapse_naturality
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (z : B ⊗[R] (A ⊗[R] M)) :
    f.lTensor C (doubleTensorCollapse μ M z) =
      doubleTensorCollapse μ N ((f.lTensor A).lTensor B z) := by
  induction z with
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul b z =>
    induction z with
    | add z w hz hw => simp only [TensorProduct.tmul_add, map_add, hz, hw]
    | tmul a m => rfl

def doubleTensorCochainMap (D : CochainComplex (ModuleCat.{u} R) ℕ) :
    HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex B (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex A D) ⟶
      HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.complex C D where
  f n := ModuleCat.ofHom (doubleTensorCollapse μ (D.X n))
  comm' i j _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact doubleTensorCollapse_naturality μ (D.d i j).hom z

theorem doubleTensorCochainMap_tmul
    (D : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) (b : B) (a : A) (x : D.X n) :
    (doubleTensorCochainMap μ D).f n (b ⊗ₜ[R] (a ⊗ₜ[R] x)) = μ (b ⊗ₜ[R] a) ⊗ₜ[R] x := rfl

theorem doubleTensorCochainMap_naturality
    {D E : CochainComplex (ModuleCat.{u} R) ℕ} (φ : D ⟶ E) :
    doubleTensorCochainMap μ D ≫ HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map C φ =
      HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map B (HilbertConstruction.Module.TensorFunctor.ModuleTensorFunctor.map A φ) ≫ doubleTensorCochainMap μ E := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact doubleTensorCollapse_naturality μ (φ.f n).hom z

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DoubleTensorCochainMap
