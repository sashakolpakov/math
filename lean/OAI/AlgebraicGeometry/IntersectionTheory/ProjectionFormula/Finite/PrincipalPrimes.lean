import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.UnitFractions

/-! # Principal Primes -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.PrincipalPrimes

noncomputable section

/-! The height-one primes containing a nonzero element form a finite
set. Their local unit fractions admit one common numerator and denominator. -/

open scoped Classical

universe u v

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]

theorem finite (f : R) (hf : f ≠ 0) :
    {p : PrimeSpectrum R | p.asIdeal.height = 1 ∧ f ∈ p.asIdeal}.Finite := by
  have hfin : {p : PrimeSpectrum R | p.asIdeal ∈ (Ideal.span {f}).minimalPrimes}.Finite :=
    ((Ideal.span {f}).finite_minimalPrimes_of_isNoetherianRing R).preimage
      (fun _ _ _ _ h => PrimeSpectrum.ext h)
  apply hfin.subset
  intro p hp
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le
    (show Ideal.span {f} ≤ p.asIdeal from Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hp.2))
  let := hq.isPrime
  have hq₀ : q ≠ ⊥ := by
    intro he
    have h := hq.le (Ideal.subset_span (Set.mem_singleton f))
    exact hf (by simpa only [he, Submodule.mem_bot] using h)
  have he : q = p.asIdeal := q.eq_of_le_of_height_le hqp (by
    rw [hp.1]
    exact Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hq₀))
  change p.asIdeal ∈ (Ideal.span {f}).minimalPrimes
  exact he ▸ hq

theorem exists_fraction (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (f : R) (hf : f ≠ 0) (z : K) (hz : z ≠ 0)
    (hlocal : ∀ p : PrimeSpectrum R, p.asIdeal.height = 1 → f ∈ p.asIdeal →
      ∃ a b : R, a ∉ p.asIdeal ∧ b ∉ p.asIdeal ∧
        z = algebraMap R K a / algebraMap R K b) :
    ∃ a b : R, a ≠ 0 ∧ b ≠ 0 ∧
      (∀ p : PrimeSpectrum R, p.asIdeal.height = 1 → f ∈ p.asIdeal →
        a ∉ p.asIdeal ∧ b ∉ p.asIdeal) ∧
      z = algebraMap R K a / algebraMap R K b := by
  let S := {p : PrimeSpectrum R | p.asIdeal.height = 1 ∧ f ∈ p.asIdeal}
  let : Fintype S := (finite R f hf).fintype
  by_cases hS : Nonempty S
  · let : Nonempty S := hS
    obtain ⟨a, b, hab, he⟩ := UnitFractions.exists_fraction R K
      (fun p : S => p.val) z (fun p => hlocal p.val p.property.1 p.property.2)
    let p : S := Classical.choice hS
    refine ⟨a, b, ?_, ?_, fun q hq hqf => hab ⟨q, hq, hqf⟩, he⟩
    · intro ha
      exact (hab p).1 (ha ▸ p.val.asIdeal.zero_mem)
    · intro hb
      exact (hab p).2 (hb ▸ p.val.asIdeal.zero_mem)
  · obtain ⟨a, b, hb, he⟩ := IsFractionRing.div_surjective R z
    refine ⟨a, b, ?_, mem_nonZeroDivisors_iff_ne_zero.mp hb, ?_, he.symm⟩
    · intro ha
      apply hz
      rw [← he, ha, map_zero, zero_div]
    · intro p hp hfp
      exact (hS ⟨⟨p, hp, hfp⟩⟩).elim

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.PrincipalPrimes
