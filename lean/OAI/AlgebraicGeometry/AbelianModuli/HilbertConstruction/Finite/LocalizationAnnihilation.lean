import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Noetherian.Basic

/-! # Localization Annihilation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.LocalizationAnnihilation

noncomputable section

/- Adapted from the corresponding IntegralModel finite-module argument, in the isolated HilbertConstruction namespace and at default computation limits. -/

open scoped BigOperators
universe u v w t

theorem finite_localization_subsingleton_iff_exists_annihilator
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (S : Submonoid R)
    {N : Type w} [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) [IsLocalizedModule S g] :
    Subsingleton N ↔ ∃ r ∈ S, r ∈ Module.annihilator R M := by
  classical
  rw [IsLocalizedModule.subsingleton_iff S g]
  constructor
  · intro h
    obtain ⟨s, hs⟩ := ‹Module.Finite R M›
    choose r hr hrz using (fun m : s => h m.val)
    refine ⟨s.attach.prod r, S.prod_mem (fun m _ => hr m), ?_⟩
    rw [← Submodule.annihilator_top, ← hs, Submodule.mem_annihilator_span]
    intro m
    obtain ⟨a, ha⟩ := Finset.dvd_prod_of_mem r (Finset.mem_attach s m)
    rw [ha, mul_comm, mul_smul, hrz, smul_zero]
  · rintro ⟨r, hr, ha⟩ m
    exact ⟨r, hr, (Module.mem_annihilator.mp ha) m⟩

theorem finite_away_subsingleton_iff_pow_annihilator
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (r : R)
    {N : Type w} [AddCommGroup N] [Module R N]
    (g : M →ₗ[R] N) [IsLocalizedModule.Away r g] :
    Subsingleton N ↔ ∃ n : ℕ, r ^ n ∈ Module.annihilator R M := by
  rw [finite_localization_subsingleton_iff_exists_annihilator (Submonoid.powers r) g]
  constructor
  · rintro ⟨s, ⟨n, rfl⟩, hs⟩
    exact ⟨n, hs⟩
  · rintro ⟨n, hn⟩
    exact ⟨r ^ n, ⟨n, rfl⟩, hn⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.LocalizationAnnihilation
