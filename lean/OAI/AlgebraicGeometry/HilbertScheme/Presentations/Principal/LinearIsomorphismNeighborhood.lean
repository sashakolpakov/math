import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.LinearIsomorphismOpen

/-! # Linear Isomorphism Neighborhood -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.LinearIsomorphismNeighborhood

noncomputable section

/-! A localized isomorphism with finite kernel and cokernel extends to
an actual principal open neighborhood. -/

open _root_.TopologicalSpace

universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

theorem localizedAway_subsingleton_of_principalOpen (M : Type v) [AddCommGroup M] [Module R M]
    (r : R) (h : ∀ p : PrimeSpectrum R, r ∉ p.asIdeal →
      Subsingleton (LocalizedModule p.asIdeal.primeCompl M)) :
    Subsingleton (LocalizedModule.Away r M) := by
  apply LocalizedModule.subsingleton_iff_support_subset.mpr
  intro p hp a ha
  obtain rfl : a = r := Set.mem_singleton_iff.mp ha
  by_contra hr
  exact (Module.notMem_support_iff.mpr (h p hr)) hp

theorem localizedLinearMap_away_bijective_of_principalOpen (f : M →ₗ[R] N)
    (r : R) (h : ∀ p : PrimeSpectrum R, r ∉ p.asIdeal →
      Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl f)) :
    Function.Bijective (LocalizedModule.map (Submonoid.powers r) f) := by
  constructor
  · apply (Localized.KernelDetection.localizedMap_injective_iff_subsingleton_kernel _ f).mpr
    apply localizedAway_subsingleton_of_principalOpen f.ker r
    intro p hp
    exact (Localized.KernelDetection.localizedMap_injective_iff_subsingleton_kernel _ f).mp (h p hp).1
  · apply (LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker _ f).mpr
    apply localizedAway_subsingleton_of_principalOpen (N ⧸ f.range) r
    intro p hp
    exact (LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker _ f).mp (h p hp).2

theorem exists_principalOpen_linear_isomorphism (f : M →ₗ[R] N)
    [Module.Finite R f.ker] [Module.Finite R (N ⧸ f.range)]
    (p : PrimeSpectrum R) (hp : Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl f)) :
    ∃ r ∉ p.asIdeal, Function.Bijective (LocalizedModule.map (Submonoid.powers r) f) := by
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hpr, hr⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp (Presentations.Finite.LinearIsomorphismOpen.isOpen_localizedLinearIsomorphismLocus f)
  exact ⟨r, hpr, localizedLinearMap_away_bijective_of_principalOpen f r (fun p hp => hr hp)⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.LinearIsomorphismNeighborhood
