import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CokernelCompletion
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Completion Cokernel Eq -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CompletionCokernelEq.Construction.CompletionCokernel

noncomputable section

/-! The cokernel of the reduced differential agrees with the original cokernel. -/

universe u v w z

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {F : Type z} [AddCommGroup F] [Module R F]
variable (f : M →ₗ[R] N) (v : F →ₗ[R] N)

def map : F →ₗ[R] N ⧸ f.range := f.range.mkQ.comp v

theorem surjective (h : Function.Surjective (f.coprod v)) :
    Function.Surjective (map f v) := by
  intro y
  obtain ⟨z, rfl⟩ := f.range.mkQ_surjective y
  obtain ⟨⟨m, x⟩, hx⟩ := h z
  refine ⟨x, ?_⟩
  change f.range.mkQ (v x) = f.range.mkQ z
  have hmf : f.range.mkQ (f m) = 0 := by
    apply (Submodule.Quotient.mk_eq_zero f.range).mpr
    exact ⟨m, rfl⟩
  have hz : f m + v x = z := hx
  rw [← hz, map_add, hmf, zero_add]

theorem kernel_eq_range :
    (map f v).ker = (CokernelCompletion.Construction.CokernelCompletionKernel.projection f v).range := by
  ext x
  constructor
  · intro hx
    have hv : v x ∈ f.range := (Submodule.Quotient.mk_eq_zero f.range).mp hx
    obtain ⟨m, hm⟩ := hv
    let y : (f.coprod v).ker := ⟨(-m, x), by
      change f (-m) + v x = 0
      rw [map_neg, hm, neg_add_cancel]⟩
    exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩
    change f.range.mkQ (v y.val.2) = 0
    apply (Submodule.Quotient.mk_eq_zero f.range).mpr
    refine ⟨-y.val.1, ?_⟩
    have hy : f y.val.1 + v y.val.2 = 0 := y.property
    rw [map_neg]
    exact neg_eq_iff_add_eq_zero.mpr hy

def iso (h : Function.Surjective (f.coprod v)) :
    (F ⧸ (CokernelCompletion.Construction.CokernelCompletionKernel.projection f v).range) ≃ₗ[R] (N ⧸ f.range) :=
  (Submodule.quotEquivOfEq _ _ (kernel_eq_range f v).symm).trans
    ((map f v).quotKerEquivOfSurjective (surjective f v h))

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CompletionCokernelEq.Construction.CompletionCokernel
