import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Data.Fintype.Sigma

/-! # Regular Linear Combination -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.RegularLinearCombination.Construction

noncomputable section

/-! Over an infinite field, a linear family of coefficients that avoids
each associated prime separately contains a simultaneous non-zero-divisor
on every module in a finite family. -/

theorem smul_injective_of_avoids_associatedPrimes
    {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] (a : R)
    (ha : ∀ p ∈ associatedPrimes R M, a ∉ p) :
    Function.Injective (fun x : M => a • x) := by
  intro x y hxy
  change a • x = a • y at hxy
  apply sub_eq_zero.mp
  by_contra hne
  have hz : a • (x - y) = 0 := by rw [smul_sub, hxy, sub_self]
  have hm : a ∈ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
    rw [biUnion_associatedPrimes_eq_zero_divisors]
    exact ⟨x - y, hne, hz⟩
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hm
  obtain ⟨hp, ham⟩ := Set.mem_iUnion.mp hp
  exact ha p hp ham

universe u v w z

theorem exists_simultaneous_regular_linear_combination
    {K : Type u} [Field K] [Infinite K]
    {V : Type v} [AddCommGroup V] [Module K V]
    {ι : Type w} [Finite ι]
    (R : ι → Type z) [∀ i, CommRing (R i)] [∀ i, IsNoetherianRing (R i)]
    [∀ i, Algebra K (R i)]
    (M : ι → Type z) [∀ i, AddCommGroup (M i)] [∀ i, Module (R i) (M i)]
    [∀ i, Module.Finite (R i) (M i)]
    (a : ∀ i, V →ₗ[K] R i)
    (h : ∀ i p, p ∈ associatedPrimes (R i) (M i) → ∃ v : V, a i v ∉ p) :
    ∃ v : V, ∀ i, Function.Injective (fun x : M i => a i v • x) := by
  classical
  let I := Σ i, {p : Ideal (R i) // p ∈ associatedPrimes (R i) (M i)}
  let (i : ι) : Fintype {p : Ideal (R i) // p ∈ associatedPrimes (R i) (M i)} :=
    (associatedPrimes.finite (R i) (M i)).fintype
  let : Fintype ι := Fintype.ofFinite ι
  have : Finite I := inferInstanceAs (Finite (Σ i, {p : Ideal (R i) //
    p ∈ associatedPrimes (R i) (M i)}))
  let B : I → Submodule K V := fun t => (t.2.1.restrictScalars K).comap (a t.1)
  have hB (t : I) : B t ≠ ⊤ := by
    obtain ⟨v, hv⟩ := h t.1 t.2.1 t.2.2
    intro he
    exact hv (show v ∈ B t from he.symm ▸ Submodule.mem_top)
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top B hB
  refine ⟨v, fun i => smul_injective_of_avoids_associatedPrimes (a i v) ?_⟩
  intro p hp
  exact hv ⟨i, p, hp⟩

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.RegularLinearCombination.Construction
