import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-! # Localized Composite Kernel -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedCompositeKernel.Constructions

/-! If the second kernel vanishes locally, a surjective first map
identifies the localized composite kernel with its own localized
kernel. The proof lifts the denominator witnessing local vanishing. -/

universe u
variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
  (f : A →+* B) (g : B →+* C) (hf : Function.Surjective f) (q : PrimeSpectrum B)

include hf

theorem kernel_comp_map_eq
    (hg : (RingHom.ker g).map (algebraMap B (Localization.AtPrime q.asIdeal)) = ⊥) :
    (RingHom.ker (g.comp f)).map
      (algebraMap A (Localization.AtPrime (q.asIdeal.comap f))) =
    (RingHom.ker f).map (algebraMap A (Localization.AtPrime (q.asIdeal.comap f))) := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    have hy : algebraMap B (Localization.AtPrime q.asIdeal) (f x) = 0 := by
      have hfx : f x ∈ RingHom.ker g := hx
      have hmem := Ideal.mem_map_of_mem (algebraMap B (Localization.AtPrime q.asIdeal)) hfx
      rw [hg] at hmem
      exact hmem
    obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff q.asIdeal.primeCompl
      (Localization.AtPrime q.asIdeal) (f x)).mp hy
    obtain ⟨a, ha⟩ := hf s
    apply (IsLocalization.algebraMap_mem_map_algebraMap_iff (q.asIdeal.comap f).primeCompl
      (Localization.AtPrime (q.asIdeal.comap f)) (RingHom.ker f) x).mpr
    refine ⟨a, ?_, ?_⟩
    · change f a ∉ q.asIdeal
      rw [ha]
      exact s.property
    · change f (a * x) = 0
      rw [map_mul, ha]
      exact hs
  · apply Ideal.map_mono
    intro x hx
    change g (f x) = 0
    change f x = 0 at hx
    rw [hx, map_zero]

theorem kernel_comp_map_eq_at (p : PrimeSpectrum A) (hp : q.asIdeal.comap f = p.asIdeal)
    (hg : (RingHom.ker g).map (algebraMap B (Localization.AtPrime q.asIdeal)) = ⊥) :
    (RingHom.ker (g.comp f)).map (algebraMap A (Localization.AtPrime p.asIdeal)) =
      (RingHom.ker f).map (algebraMap A (Localization.AtPrime p.asIdeal)) := by
  have hprime : PrimeSpectrum.comap f q = p := PrimeSpectrum.ext hp
  subst p
  exact kernel_comp_map_eq A B C f g hf q hg

end OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedCompositeKernel.Constructions
