import Mathlib

/-! # Linear Components -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Filtered.LinearComponents

noncomputable section

/-! Images of independently defined filtrations commute with an actual component decomposition and a compatible linear map. -/

variable {R : Type*} [CommRing R] {ι : Type*}
  {A B : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
  {A' B' : ι → Type*} [∀ i, AddCommGroup (A' i)] [∀ i, Module R (A' i)]
  [∀ i, AddCommGroup (B' i)] [∀ i, Module R (B' i)]
  (e : A ≃ₗ[R] ∀ i, A' i) (d : B ≃ₗ[R] ∀ i, B' i)
  (f : A →ₗ[R] B) (g : ∀ i, A' i →ₗ[R] B' i)
  (S : Submodule R A) (T : ∀ i, Submodule R (A' i))
  (hS : ∀ a, a ∈ S ↔ ∀ i, e a i ∈ T i)
  (hf : ∀ a i, d (f a) i = g i (e a i))

include hS hf in
theorem mem_map_iff_components (b : B) :
    b ∈ S.map f ↔ ∀ i, ∃ a : A' i, a ∈ T i ∧ g i a = d b i := by
  constructor
  · rintro ⟨a, ha, rfl⟩ i
    exact ⟨e a i, (hS a).mp ha i, (hf a i).symm⟩
  · intro h
    choose a ha hab using h
    let z := e.symm a
    have hz : e z = a := e.apply_symm_apply a
    refine ⟨z, (hS z).mpr ?_, ?_⟩
    · intro i
      rw [hz]
      exact ha i
    · apply d.injective
      funext i
      rw [hf, hz]
      exact hab i

end

end OAI.AlgebraicGeometry.Comparison.Betti.Filtered.LinearComponents
