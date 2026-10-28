import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Multiplicity
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-! # Max Domain -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.MaxDomain

noncomputable section

/-! A noetherian local ring with a nonnilpotent generator of its maximal
ideal is a domain. Krull intersection supplies the exact finite order
of every nonzero element, without assuming cancellation in advance. -/

open IsLocalRing

universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  (r : R) (hm : maximalIdeal R = Ideal.span {r})

include hm

theorem exists_unit_factor (a : R) (ha : a ≠ 0) :
    ∃ (n : ℕ) (u : Rˣ), a = r ^ n * u := by
  have hf : FiniteMultiplicity r a := by
    by_contra hn
    have hpow := FiniteMultiplicity.not_iff_forall.mp hn
    apply ha
    have hi : a ∈ ⨅ n : ℕ, maximalIdeal R ^ n := by
      apply Ideal.mem_iInf.mpr
      intro n
      rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact hpow n
    rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal R)
      (maximalIdeal.isMaximal R).ne_top, Submodule.mem_bot] at hi
  obtain ⟨b, hab, hb⟩ := hf.exists_eq_pow_mul_and_not_dvd
  have hu : IsUnit b := IsLocalRing.notMem_maximalIdeal.mp (by
    rw [hm, Ideal.mem_span_singleton]
    exact hb)
  obtain ⟨u, rfl⟩ := hu
  exact ⟨multiplicity r a, u, hab⟩

theorem domain (hnil : ¬IsNilpotent r) : IsDomain R := by
  let : NoZeroDivisors R := ⟨by
    intro a b hab
    by_cases ha : a = 0
    · exact Or.inl ha
    by_cases hb : b = 0
    · exact Or.inr hb
    exfalso
    obtain ⟨n, u, rfl⟩ := exists_unit_factor R r hm a ha
    obtain ⟨k, v, rfl⟩ := exists_unit_factor R r hm b hb
    have he : (r ^ n * ↑u) * (r ^ k * ↑v) = r ^ (n + k) * ↑(u * v) := by
      rw [pow_add, Units.val_mul]
      ring
    rw [he] at hab
    have hz : r ^ (n + k) = 0 := (Units.mul_left_eq_zero (u * v)).mp hab
    exact hnil ⟨n + k, hz⟩⟩
  exact NoZeroDivisors.to_isDomain R

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.MaxDomain
