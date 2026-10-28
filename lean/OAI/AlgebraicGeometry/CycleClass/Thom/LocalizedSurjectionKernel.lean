import OAI.AlgebraicGeometry.CycleClass.Thom.SurjectiveLocalRingMap
import Mathlib.RingTheory.Localization.Ideal

/-! # Localized Surjection Kernel -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedSurjectionKernel.Constructions

noncomputable section

/-! The kernel of the native localized map of a surjection is the
localization of its original kernel, proved directly with fractions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

theorem localRingHom_kernel (f : R →+* S) (hf : Function.Surjective f) (q : PrimeSpectrum S) :
    RingHom.ker (Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl) =
      (RingHom.ker f).map (algebraMap R (Localization.AtPrime (q.asIdeal.comap f))) := by
  ext z
  obtain ⟨r, t, rfl⟩ := IsLocalization.exists_mk'_eq (q.asIdeal.comap f).primeCompl z
  change Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl
    (IsLocalization.mk' (Localization.AtPrime (q.asIdeal.comap f)) r t) = 0 ↔ _
  rw [Localization.localRingHom_mk', IsLocalization.mk'_eq_zero_iff,
    IsLocalization.mk'_mem_map_algebraMap_iff (q.asIdeal.comap f).primeCompl]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨a, ha⟩ := hf s.val
    refine ⟨a, ?_, ?_⟩
    · change f a ∉ q.asIdeal
      exact (congrArg (fun b : S => b ∉ q.asIdeal) ha).mpr s.property
    · change f (a * r) = 0
      rw [map_mul, ha]
      exact hs
  · rintro ⟨a, ha, hz⟩
    refine ⟨⟨f a, ha⟩, ?_⟩
    change f (a * r) = 0 at hz
    exact (map_mul f a r).symm.trans hz

end

end OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedSurjectionKernel.Constructions
