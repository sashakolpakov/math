import OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.InverseLimit
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Tensor Inverse Limit -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TensorInverseLimit.FiniteTensorInverseLimit

noncomputable section

/-!
# Tensoring with a finite free module commutes with compatible sections

A finite basis turns the tensor product into finitely many coefficient
coordinates. Taking compatible systems commutes with those coordinates,
yielding an explicit inverse-limit tensor isomorphism.
-/

open scoped TensorProduct

open Classical

universe u

variable (R ξ : Type u) [CommRing R]
  (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

def piMap (f : M →ₗ[R] N) : (ξ → M) →ₗ[R] (ξ → N) :=
  LinearMap.pi (fun i => f.comp (LinearMap.proj i))

variable (V : Type u) [AddCommGroup V] [Module R V] [Fintype ξ] (b : Module.Basis ξ R V)

def coordinateEquiv : M ⊗[R] V ≃ₗ[R] (ξ → M) :=
  (TensorProduct.congr (LinearEquiv.refl R M) b.equivFun).trans (TensorProduct.piScalarRight R R M ξ)

theorem coordinateEquiv_tmul (m : M) (v : V) (i : ξ) :
    coordinateEquiv R ξ M V b (m ⊗ₜ[R] v) i = b.equivFun v i • m := rfl

theorem coordinate_naturality (f : M →ₗ[R] N) :
    (coordinateEquiv R ξ N V b).toLinearMap.comp (TensorProduct.map f LinearMap.id) =
      (piMap R ξ M N f).comp (coordinateEquiv R ξ M V b).toLinearMap := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro m
  apply LinearMap.ext
  intro v
  funext i
  change b.equivFun v i • f m = f (b.equivFun v i • m)
  exact (f.map_smul _ _).symm

variable (A : ℕ → Type u) [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
  (t : ∀ n m, n ≤ m → A m →ₗ[R] A n)

def tensorTransition (n m : ℕ) (hnm : n ≤ m) : A m ⊗[R] V →ₗ[R] A n ⊗[R] V :=
  TensorProduct.map (t n m hnm) LinearMap.id

def piTransition (n m : ℕ) (hnm : n ≤ m) : (ξ → A m) →ₗ[R] (ξ → A n) :=
  piMap R ξ (A m) (A n) (t n m hnm)

local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible R A t
local notation "CT" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible R (fun n => A n ⊗[R] V) (OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TensorInverseLimit.FiniteTensorInverseLimit.tensorTransition R V A t)
local notation "CP" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible R (fun n => ξ → A n) (OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TensorInverseLimit.FiniteTensorInverseLimit.piTransition R ξ A t)

def piCompatibleEquiv : CP ≃ₗ[R] (ξ → C) where
  toFun x i := ⟨fun n => x.val n i, fun n m hnm => congrFun (x.property n m hnm) i⟩
  invFun x := ⟨fun n i => (x i).val n, fun n m hnm => funext (fun i => (x i).property n m hnm)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := funext (fun _ => Subtype.ext rfl)
  map_add' _ _ := funext (fun _ => Subtype.ext rfl)
  map_smul' _ _ := funext (fun _ => Subtype.ext rfl)

def diagramEquiv : CT ≃ₗ[R] CP :=
  Cohomology.Module.InverseLimit.ModuleInverseLimit.equiv R (fun n => A n ⊗[R] V) (tensorTransition R V A t)
    (fun n => ξ → A n) (piTransition R ξ A t) (fun n => coordinateEquiv R ξ (A n) V b)
    (fun n m hnm a => LinearMap.congr_fun (coordinate_naturality R ξ (A m) (A n) V b (t n m hnm)) a)

/-- Tensoring compatible sections with a finite free module gives compatible tensor sections. -/
def equiv : C ⊗[R] V ≃ₗ[R] CT :=
  (coordinateEquiv R ξ C V b).trans (piCompatibleEquiv R ξ A t).symm |>.trans
    (diagramEquiv R ξ V b A t).symm

theorem equiv_eval (n : ℕ) (z : C ⊗[R] V) :
    Cohomology.Module.InverseLimit.ModuleInverseLimit.eval R (fun n => A n ⊗[R] V) (tensorTransition R V A t) n
      (equiv R ξ V b A t z) = TensorProduct.map (Cohomology.Module.InverseLimit.ModuleInverseLimit.eval R A t n) LinearMap.id z := by
  apply (coordinateEquiv R ξ (A n) V b).injective
  change coordinateEquiv R ξ (A n) V b
    ((coordinateEquiv R ξ (A n) V b).symm (fun i => (coordinateEquiv R ξ C V b z i).val n)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact (LinearMap.congr_fun (coordinate_naturality R ξ C (A n) V b (Cohomology.Module.InverseLimit.ModuleInverseLimit.eval R A t n)) z).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TensorInverseLimit.FiniteTensorInverseLimit
