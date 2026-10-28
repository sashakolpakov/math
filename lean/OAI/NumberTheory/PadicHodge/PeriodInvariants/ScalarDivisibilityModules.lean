import OAI.NumberTheory.PadicHodge.PeriodInvariants.FiniteTensorCoordinates
import Mathlib.Data.Finsupp.Basic
import Mathlib.RingTheory.Ideal.Operations

/-! # Scalar Divisibility Modules -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.ScalarDivisibilityModules

noncomputable section

/-! # Scalar divisibility in finite tensors, finite-support modules, and principal filtrations -/

open scoped Pointwise

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

theorem principal_power_mem (r : R) (n : ℕ) (x : M) :
    x ∈ ((Ideal.span {r}) ^ n • ⊤ : Submodule R M) ↔ ∃ y, r ^ n • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and]

theorem finsupp_divisible {I : Type*} (r : R) (x : I →₀ M) :
    (∃ y, r • y = x) ↔ ∀ i, ∃ y, r • y = x i := by
  change x ∈ Set.range (Finsupp.mapRange (fun m : M => r • m) (smul_zero r)) ↔ _
  rw [Finsupp.range_mapRange]
  rfl

variable {N J : Type*} [AddCommGroup N] [Module R N]

theorem coordinates_divisible (e : M ≃ₗ[R] (J → N)) (r : R) (x : M) :
    (∃ y, r • y = x) ↔ ∀ j, ∃ y, r • y = e x j := by
  constructor
  · rintro ⟨y, hy⟩ j
    refine ⟨e y j, ?_⟩
    exact (congrFun (map_smul e r y) j).symm.trans (congrArg (fun z => e z j) hy)
  · intro h
    choose y hy using h
    refine ⟨e.symm y, ?_⟩
    apply e.injective
    rw [map_smul, LinearEquiv.apply_symm_apply]
    funext j
    exact hy j

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.ScalarDivisibilityModules
