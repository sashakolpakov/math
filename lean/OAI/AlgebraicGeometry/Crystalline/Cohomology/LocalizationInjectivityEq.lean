import OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizationRange

/-! # Localization Injectivity Eq -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizationInjectivityEq.LocalizationInjectivity

noncomputable section

/-!
# Injectivity detected on principal localizations

The unit-ideal criterion detects zero elements, and therefore injectivity,
from a family of principal module localizations.
-/

universe u

variable (R ι M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
  (s : ι → R) (ML : ι → Type u) [∀ i, AddCommGroup (ML i)] [∀ i, Module R (ML i)]
  (m : ∀ i, M →ₗ[R] ML i)
  [∀ i, IsLocalizedModule (Submonoid.powers (s i)) (m i)]

theorem eq_zero (hs : Ideal.span (Set.range s) = ⊤) (x : M) (hx : ∀ i, m i x = 0) : x = 0 := by
  have h : x ∈ (⊥ : Submodule R M) := by
    apply Submodule.mem_of_span_eq_top_of_smul_pow_mem (⊥ : Submodule R M) (Set.range s) hs x
    intro r
    obtain ⟨i, hi⟩ := r.property
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (s i))
      (f := m i) ((hx i).trans (map_zero (m i)).symm)
    obtain ⟨n, hn⟩ := t.property
    change s i ^ n = (t : R) at hn
    refine ⟨n, ?_⟩
    change (r : R) ^ n • x = 0
    change (t : R) • x = (t : R) • (0 : M) at ht
    rw [← hi, hn]
    exact ht.trans (smul_zero _)
  exact h

theorem injective (N : Type u) [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (NL : ι → Type u) [∀ i, AddCommGroup (NL i)] [∀ i, Module R (NL i)]
    (n : ∀ i, N →ₗ[R] NL i) (fl : ∀ i, ML i →ₗ[R] NL i)
    (commute : ∀ i x, n i (f x) = fl i (m i x))
    (hs : Ideal.span (Set.range s) = ⊤) (hl : ∀ i, Function.Injective (fl i)) :
    Function.Injective f := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply eq_zero R ι M s ML m hs
  intro i
  rw [map_sub, sub_eq_zero]
  apply hl i
  rw [← commute, hxy, commute]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizationInjectivityEq.LocalizationInjectivity
