import OAI.ArithmeticGeometry.Models.SpreadingOut.GenericFlatness
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Fiber Regularity -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.FiberRegularity.Construction

noncomputable section

/-! Flatness of a principal quotient preserves its defining non-zero-divisor
under arbitrary scalar extension. -/

open scoped TensorProduct

universe u

theorem tensor_mul_injective_of_flat_quotient
    (R B k : Type u) [CommRing R] [CommRing B] [CommRing k]
    [Algebra R B] [Algebra R k] (b : B)
    (hb : Function.Injective (fun x : B ↦ b * x))
    [Module.Flat R (B ⧸ Ideal.span ({b} : Set B))] :
    Function.Injective (fun x : k ⊗[R] B ↦ (1 ⊗ₜ[R] b) * x) := by
  let I := Ideal.span ({b} : Set B)
  let π : B →ₗ[R] B ⧸ I := (Ideal.Quotient.mkₐ R I).toLinearMap
  let f : B →ₗ[R] B := LinearMap.mulLeft R b
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have h : Function.Exact f π := by
    intro y
    change Ideal.Quotient.mk I y = 0 ↔ ∃ x, b * x = y
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact ⟨fun ⟨x, hx⟩ ↦ ⟨x, hx.symm⟩, fun ⟨x, hx⟩ ↦ ⟨x, hx.symm⟩⟩
  have H := LinearMap.lTensor_injective_of_exact_of_flat π hπ f hb h k
  have he : f.lTensor k = LinearMap.mulLeft R (1 ⊗ₜ[R] b : k ⊗[R] B) := by
    ext x y
    change x ⊗ₜ[R] (b * y) = (1 ⊗ₜ[R] b) * (x ⊗ₜ[R] y)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [he] at H
  exact H

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.FiberRegularity.Construction
