import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TensorInverseLimit
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableForms
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableOperators

/-! # Witt Multivariable Forms -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.WittMultivariableForms

noncomputable section

/-!
# Actual completed multivariable forms as tensor modules

The natural finite-level coordinate descriptions and finite free tensor
interchange identify every term of the actual inverse-limit PD de Rham
complex with the corresponding tensor term of compatible coefficients.
-/

open Classical
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableThickening.WittMultivariableThickening.Ring p k σ
local notation "T" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableTower.WittMultivariableTower.tower p k σ
local notation "C" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.InverseLimit.PDInverseLimit.Ring p k k T
local notation "Ω" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.PDDeRham.CompletedForm p k k T

def ringTransition (n m : ℕ) (hnm : n ≤ m) : Q m →ₗ[W] Q n :=
  (MultivariableTower.WittMultivariableTower.transitionHom p k σ n m hnm).toLinearMap

def compatibleRingEquiv : Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible W Q (ringTransition p k σ) ≃ₗ[W] C where
  toFun x := ⟨x.val, fun n m hnm => x.property n m hnm⟩
  invFun x := ⟨x.val, fun n m hnm => x.property n m hnm⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

local instance formGroupFamily (j : ℕ) : ∀ n, AddCommGroup (MultivariableForms.WittMultivariableForms.Form p k σ n j) :=
  fun n => inferInstanceAs (AddCommGroup (PD.DeRham.PDDeRham.Form W (Q n)
    (RingHom.ker (MultivariableThickening.WittMultivariableThickening.reduction p k σ n))
    (MultivariableThickening.WittMultivariableThickening.kernelDividedPowers p k σ n) j))

local instance formModuleFamily (j : ℕ) : ∀ n, Module W (MultivariableForms.WittMultivariableForms.Form p k σ n j) :=
  fun n => inferInstanceAs (Module W (PD.DeRham.PDDeRham.Form W (Q n)
    (RingHom.ker (MultivariableThickening.WittMultivariableThickening.reduction p k σ n))
    (MultivariableThickening.WittMultivariableThickening.kernelDividedPowers p k σ n) j))

def formsCompatibleEquiv (j : ℕ) :
    Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible W (fun n => MultivariableForms.WittMultivariableForms.Form p k σ n j)
      (fun n m hnm => MultivariableForms.WittMultivariableForms.formMap p k σ n m hnm j) ≃ₗ[W] Ω j where
  toFun x := ⟨x.val, fun n m hnm => x.property n m hnm⟩
  invFun x := ⟨x.val, fun n m hnm => x.property n m hnm⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

variable [Fintype σ] [LinearOrder σ]

local instance indexFintype (j : ℕ) : Fintype (Set.powersetCard σ j) := Fintype.ofFinite _

def exteriorBasis (j : ℕ) : Module.Basis (Set.powersetCard σ j) W (⋀[W]^j (σ →₀ W)) :=
  (Finsupp.basisSingleOne : Module.Basis σ W (σ →₀ W)).exteriorPower j

def tensorLimitEquiv (j : ℕ) : Koszul.Tensor.KoszulTensor.Term W σ C j ≃ₗ[W]
    Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible W (fun n => Koszul.Tensor.KoszulTensor.Term W σ (Q n) j)
      (Finite.TensorInverseLimit.FiniteTensorInverseLimit.tensorTransition W (⋀[W]^j (σ →₀ W)) Q (ringTransition p k σ)) :=
  (TensorProduct.congr (compatibleRingEquiv p k σ).symm (LinearEquiv.refl W _)).trans
    (Finite.TensorInverseLimit.FiniteTensorInverseLimit.equiv W (Set.powersetCard σ j) (⋀[W]^j (σ →₀ W)) (exteriorBasis p k σ j)
      Q (ringTransition p k σ))

def tensorFormsLimitEquiv (j : ℕ) :
    Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible W (fun n => Koszul.Tensor.KoszulTensor.Term W σ (Q n) j)
      (Finite.TensorInverseLimit.FiniteTensorInverseLimit.tensorTransition W (⋀[W]^j (σ →₀ W)) Q (ringTransition p k σ)) ≃ₗ[W]
        Cohomology.Module.InverseLimit.ModuleInverseLimit.compatible W (fun n => MultivariableForms.WittMultivariableForms.Form p k σ n j)
          (fun n m hnm => MultivariableForms.WittMultivariableForms.formMap p k σ n m hnm j) :=
  Cohomology.Module.InverseLimit.ModuleInverseLimit.equiv W (fun n => Koszul.Tensor.KoszulTensor.Term W σ (Q n) j)
    (Finite.TensorInverseLimit.FiniteTensorInverseLimit.tensorTransition W (⋀[W]^j (σ →₀ W)) Q (ringTransition p k σ))
    (fun n => MultivariableForms.WittMultivariableForms.Form p k σ n j)
    (fun n m hnm => MultivariableForms.WittMultivariableForms.formMap p k σ n m hnm j)
    (fun n => (MultivariableForms.WittMultivariableForms.tensorFormsEquiv p k σ n j).restrictScalars W)
    (fun n m hnm z => MultivariableForms.WittMultivariableForms.tensorFormsEquiv_naturality p k σ n m hnm j z)

/-- The actual compatible PD forms are the tensor forms of the compatible coefficient ring. -/
def formsEquiv (j : ℕ) : Koszul.Tensor.KoszulTensor.Term W σ C j ≃ₗ[W] Ω j :=
  (tensorLimitEquiv p k σ j).trans (tensorFormsLimitEquiv p k σ j) |>.trans (formsCompatibleEquiv p k σ j)

theorem tensorLimitEquiv_eval (j n : ℕ) (z : Koszul.Tensor.KoszulTensor.Term W σ C j) :
    (tensorLimitEquiv p k σ j z).val n =
      TensorProduct.map (PD.InverseLimit.PDInverseLimit.eval p k k T n).toLinearMap LinearMap.id z := by
  change Cohomology.Module.InverseLimit.ModuleInverseLimit.eval W (fun n => Q n ⊗[W] (⋀[W]^j (σ →₀ W)))
    (Finite.TensorInverseLimit.FiniteTensorInverseLimit.tensorTransition W (⋀[W]^j (σ →₀ W)) Q (ringTransition p k σ)) n
      (Finite.TensorInverseLimit.FiniteTensorInverseLimit.equiv W (Set.powersetCard σ j) (⋀[W]^j (σ →₀ W)) (exteriorBasis p k σ j)
        Q (ringTransition p k σ)
          (TensorProduct.congr (compatibleRingEquiv p k σ).symm (LinearEquiv.refl W _) z)) = _
  rw [Finite.TensorInverseLimit.FiniteTensorInverseLimit.equiv_eval]
  change TensorProduct.map (Cohomology.Module.InverseLimit.ModuleInverseLimit.eval W Q (ringTransition p k σ) n) LinearMap.id
    (TensorProduct.map (compatibleRingEquiv p k σ).symm.toLinearMap LinearMap.id z) = _
  rw [TensorProduct.map_map, LinearMap.id_comp]
  rfl

theorem formsEquiv_eval (j n : ℕ) (z : Koszul.Tensor.KoszulTensor.Term W σ C j) :
    PD.PDDeRham.eval p k k T j n (formsEquiv p k σ j z) =
      MultivariableForms.WittMultivariableForms.tensorFormsEquiv p k σ n j
        (TensorProduct.map (PD.InverseLimit.PDInverseLimit.eval p k k T n).toLinearMap LinearMap.id z) := by
  change MultivariableForms.WittMultivariableForms.tensorFormsEquiv p k σ n j ((tensorLimitEquiv p k σ j z).val n) = _
  rw [tensorLimitEquiv_eval]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.WittMultivariableForms
