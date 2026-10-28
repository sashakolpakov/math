import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.JointEigenSumIndependence
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Joint Character Decomposition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.JointCharacterDecomposition

noncomputable section

/-! The actual joint character spaces embed by their sum. When
their computed dimensions exhaust the ambient space, this gives an
explicit linear decomposition suitable for transporting bases. -/

open scoped BigOperators

variable {k V R I : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : R → V →ₗ[k] V)

def jointCharacterSpace (χ : R → k) : Submodule k V where
  carrier := {v | ∀ a, ρ a v = χ a • v}
  zero_mem' a := by rw [map_zero, smul_zero]
  add_mem' hv hw a := by rw [map_add, hv a, hw a, smul_add]
  smul_mem' c v hv a := by rw [map_smul, hv a, smul_comm]

variable [Fintype I] (χ : I → R → k)

def jointCharacterSumLinear : (∀ i, jointCharacterSpace ρ (χ i)) →ₗ[k] V where
  toFun x := ∑ i, (x i).val
  map_add' x y := by
    change (∑ i, ((x i).val + (y i).val)) = (∑ i, (x i).val) + ∑ i, (y i).val
    exact Finset.sum_add_distrib
  map_smul' c x := by
    change (∑ i, c • (x i).val) = c • ∑ i, (x i).val
    rw [Finset.smul_sum]

theorem jointCharacterSumLinear_injective (hχ : Function.Injective χ) :
    Function.Injective (jointCharacterSumLinear ρ χ) := by
  intro x y h
  have hsum : ∑ i, ((x i).val - (y i).val) = 0 := by
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr h
  have he : ∀ i ∈ (Finset.univ : Finset I), ∀ a,
      ρ a ((x i).val - (y i).val) = χ i a • ((x i).val - (y i).val) := by
    intro i _ a
    rw [map_sub, (x i).property a, (y i).property a, smul_sub]
  have hz := JointEigenSumIndependence.jointEigenvectors_sum_eq_zero ρ χ hχ Finset.univ
    (fun i => (x i).val - (y i).val) he hsum
  funext i
  exact Subtype.ext (sub_eq_zero.mp (hz i (Finset.mem_univ i)))

def jointCharacterDecomposition [FiniteDimensional k V] (hχ : Function.Injective χ)
    (hdim : (∑ i, Module.finrank k (jointCharacterSpace ρ (χ i))) = Module.finrank k V) :
    (∀ i, jointCharacterSpace ρ (χ i)) ≃ₗ[k] V :=
  (jointCharacterSumLinear ρ χ).linearEquivOfInjective (jointCharacterSumLinear_injective ρ χ hχ)
    (by rw [Module.finrank_pi_fintype]; exact hdim)

theorem jointCharacterDecomposition_apply [FiniteDimensional k V] (hχ : Function.Injective χ)
    (hdim : (∑ i, Module.finrank k (jointCharacterSpace ρ (χ i))) = Module.finrank k V)
    (x : ∀ i, jointCharacterSpace ρ (χ i)) :
    jointCharacterDecomposition ρ χ hχ hdim x = ∑ i, (x i).val := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.JointCharacterDecomposition
