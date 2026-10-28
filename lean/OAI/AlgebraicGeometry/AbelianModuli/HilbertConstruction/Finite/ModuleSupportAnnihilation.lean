import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.LocalizationAnnihilation

/-! # Module Support Annihilation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ModuleSupportAnnihilation

noncomputable section

/- Adapted from the corresponding IntegralModel finite-module argument, in the isolated HilbertConstruction namespace and at default computation limits. -/

open scoped BigOperators
universe u v w t

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

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.ModuleSupportAnnihilation
