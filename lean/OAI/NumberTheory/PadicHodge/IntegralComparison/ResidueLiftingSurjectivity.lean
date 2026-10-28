import Mathlib.RingTheory.Nakayama

/-! # Residue Lifting Surjectivity -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ResidueLiftingSurjectivity

/-! A map onto an actual residue module generates the original finite module. -/

universe u v w z

variable {R : Type u} [CommRing R]
  {L : Type v} [AddCommGroup L] [Module R L]
  {M : Type w} [AddCommGroup M] [Module R M] [Module.Finite R M]
  {N : Type z} [AddCommGroup N] [Module R N]

theorem surjective_of_lifts (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson)
    (f : L →ₗ[R] M)
    (hs : ∀ x : M, ∃ y : L, f y - x ∈ I • (⊤ : Submodule R M)) :
    Function.Surjective f := by
  apply LinearMap.surjective_of_surjective_comp_mkQ f I hI
  intro q
  obtain ⟨x, rfl⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective q
  obtain ⟨y, hy⟩ := hs x
  exact ⟨y, (Submodule.Quotient.eq _).mpr hy⟩

theorem surjective (I : Ideal R) (hI : I ≤ (⊥ : Ideal R).jacobson)
    (f : L →ₗ[R] M) (g : M →ₗ[R] N) (hk : LinearMap.ker g = I • (⊤ : Submodule R M))
    (hs : ∀ x : N, ∃ y : L, g (f y) = x) : Function.Surjective f := by
  apply LinearMap.surjective_of_surjective_comp_mkQ f I hI
  intro q
  obtain ⟨x, rfl⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective q
  obtain ⟨y, hy⟩ := hs (g x)
  refine ⟨y, (Submodule.Quotient.eq _).mpr ?_⟩
  rw [← hk, LinearMap.mem_ker, map_sub]
  exact sub_eq_zero.mpr hy

end OAI.NumberTheory.PadicHodge.IntegralComparison.ResidueLiftingSurjectivity
