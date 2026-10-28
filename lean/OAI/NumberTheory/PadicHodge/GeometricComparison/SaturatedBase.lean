import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.LinearAlgebra.Quotient.Defs

/-! # Saturated Base -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SaturatedBase.SaturatedBaseChange

noncomputable section

/-! A submodule with flat quotient is detected before a faithful scalar extension. -/

open scoped TensorProduct

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [FaithfulSMul R S] [AddCommGroup M] [Module R M]
  (P : Submodule R M) [Module.Flat R (M ⧸ P)]

theorem one_tmul_mem_iff (x : M) : (1 : S) ⊗ₜ[R] x ∈ P.baseChange S ↔ x ∈ P := by
  constructor
  · rintro ⟨y, hy⟩
    have hz : (P.mkQ.baseChange S).comp (P.subtype.baseChange S) = 0 := by
      rw [← LinearMap.baseChange_comp]
      have h : P.mkQ.comp P.subtype = 0 := by
        ext z
        exact (Submodule.Quotient.mk_eq_zero P).mpr z.property
      rw [h, LinearMap.baseChange_zero]
    have ht : (1 : S) ⊗ₜ[R] P.mkQ x = 0 := by
      rw [← LinearMap.baseChange_tmul, ← hy]
      exact LinearMap.congr_fun hz y
    apply (Submodule.Quotient.mk_eq_zero P).mp
    exact (Module.Flat.tensorProduct_mk_injective (R := R) (S := S) (M := M ⧸ P))
      (ht.trans (map_zero (TensorProduct.mk R S (M ⧸ P) 1)).symm)
  · exact P.tmul_mem_baseChange_of_mem 1

theorem equiv_mem_iff {N : Type*} [AddCommGroup N] [Module S N]
    (e : S ⊗[R] M ≃ₗ[S] N) (Q : Submodule S N)
    (hQ : (P.baseChange S).map e.toLinearMap = Q) (x : M) :
    e ((1 : S) ⊗ₜ[R] x) ∈ Q ↔ x ∈ P := by
  rw [← hQ]
  constructor
  · rintro ⟨y, hy, he⟩
    have he' := e.injective he
    exact (one_tmul_mem_iff P x).mp (he' ▸ hy)
  · intro hx
    exact ⟨(1 : S) ⊗ₜ[R] x, (one_tmul_mem_iff P x).mpr hx, rfl⟩

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SaturatedBase.SaturatedBaseChange
