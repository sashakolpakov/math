import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Noetherian.Basic

/-! # Module Annihilation -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ModuleAnnihilation

noncomputable section

/-! Finite modules admit a single annihilator after vanishing on a
localization, and a power of an ideal cutting out their support annihilates them. -/

open scoped BigOperators

universe u v w

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

theorem finiteModule_support_subset_iff_power_annihilator
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) (hI : I.FG) :
    Module.support R M ⊆ PrimeSpectrum.zeroLocus (I : Set R) ↔
      ∃ n : ℕ, I ^ n ≤ Module.annihilator R M := by
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff]
  constructor
  · intro h
    exact Ideal.exists_pow_le_of_le_radical_of_fg h hI
  · rintro ⟨n, hn⟩ r hr
    exact ⟨n, hn (Ideal.pow_mem_pow hr n)⟩

theorem finiteModule_support_subset_exists_power_annihilating
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (I : Ideal R) (h : Module.support R M ⊆ PrimeSpectrum.zeroLocus (I : Set R)) :
    ∃ n : ℕ, ∀ r ∈ I ^ n, ∀ m : M, r • m = 0 := by
  obtain ⟨n, hn⟩ := (finiteModule_support_subset_iff_power_annihilator I
    I.fg_of_isNoetherianRing).mp h
  exact ⟨n, fun r hr => Module.mem_annihilator.mp (hn hr)⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.ModuleAnnihilation
