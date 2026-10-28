import OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedPrimeLength
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-! # Prime Filtration Multiplicity -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PrimeFiltrationMultiplicity.Constructions

noncomputable section

/-! At a minimal support prime, the number of repeated copies of that
prime in a filtration is exactly the actual localized module length. -/

open scoped Classical

open OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedModuleLength.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedPrimeLength.Constructions

universe u v
variable (R : Type u) [CommRing R]
  (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
  (p : PrimeSpectrum R) (hp : p.asIdeal ∈ (Module.annihilator R M).minimalPrimes)

include hp

theorem factor_not_le (q : PrimeSpectrum R)
    (hq : Module.support R (R ⧸ q.asIdeal) ⊆ Module.support R M) (hne : q ≠ p) :
    ¬ q.asIdeal ≤ p.asIdeal := by
  intro hle
  have hqm : q ∈ Module.support R M := hq (by
    rw [Module.mem_support_iff_of_finite, Ideal.annihilator_quotient])
  have he : p.asIdeal ≤ q.asIdeal := hp.2 ⟨q.isPrime, Module.mem_support_iff_of_finite.mp hqm⟩ hle
  exact hne (PrimeSpectrum.ext (le_antisymm hle he))

theorem sum_localLength_eq_count (ps : List (PrimeSpectrum R))
    (hs : ∀ q ∈ ps, Module.support R (R ⧸ q.asIdeal) ⊆ Module.support R M) :
    (ps.map (fun q => LocalizedModuleLength.Constructions.localLength R (R ⧸ q.asIdeal) p)).sum = (ps.count p : ℕ∞) := by
  classical
  induction ps with
  | nil => simp only [List.map_nil, List.sum_nil, List.count_nil, Nat.cast_zero]
  | cons q qs ih =>
    have hi := ih (fun a ha => hs a (List.mem_cons_of_mem q ha))
    rw [List.map_cons, List.sum_cons, hi]
    by_cases hq : q = p
    · subst q
      rw [LocalizedPrimeLength.Constructions.localLength_self]
      simp only [List.count_cons_self, Nat.cast_add, Nat.cast_one, add_comm]
    · rw [LocalizedPrimeLength.Constructions.localLength_prime_of_not_le R p q (factor_not_le R M p hp q
        (hs q (List.mem_cons_self)) hq), zero_add]
      simp only [List.count_cons_of_ne hq]

theorem localLength_eq_count (ps : List (PrimeSpectrum R))
    (hs : ∀ q ∈ ps, Module.support R (R ⧸ q.asIdeal) ⊆ Module.support R M)
    (hl : LocalizedModuleLength.Constructions.localLength R M p = (ps.map (fun q => LocalizedModuleLength.Constructions.localLength R (R ⧸ q.asIdeal) p)).sum) :
    LocalizedModuleLength.Constructions.localLength R M p = (ps.count p : ℕ∞) :=
  hl.trans (sum_localLength_eq_count R M p hp ps hs)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PrimeFiltrationMultiplicity.Constructions
