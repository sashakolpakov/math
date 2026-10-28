import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.PrimeLocalization
import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-! # Prime Semilocal -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.PrimeSemilocal

noncomputable section

/-! Localization away from finitely many primes is semilocal. Every
maximal ideal is the extension of one of those actual primes, with
the prescribed contraction. No height-one assumption is needed. -/

universe u v

variable (R : Type u) [CommRing R] {ι : Type v} [Fintype ι] [Nonempty ι]
  (P : ι → PrimeSpectrum R)
  (A : Type u) [CommRing A] [Algebra R A]
  [IsLocalization (PrimeLocalization.denominators R P) A]

theorem maximal_eq_map (q : Ideal A) [q.IsMaximal] :
    ∃ i, q = (P i).asIdeal.map (algebraMap R A) := by
  let M := PrimeLocalization.denominators R P
  obtain ⟨i, hi⟩ := PrimeLocalization.under_le_one_of_primes R P A q
  have hp : ((P i).asIdeal.map (algebraMap R A)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M A (P i).asIdeal (P i).isPrime
      (PrimeLocalization.disjoint_denominators R P i)
  refine ⟨i, Ideal.IsMaximal.eq_of_le (inferInstance : q.IsMaximal) hp.ne_top ?_⟩
  rw [← IsLocalization.map_under M A q]
  exact Ideal.map_mono hi

theorem maximal_contraction (q : Ideal A) [q.IsMaximal] :
    ∃ i, q.under R = (P i).asIdeal := by
  obtain ⟨i, hi⟩ := maximal_eq_map R P A q
  exact ⟨i, (congrArg (Ideal.under R) hi).trans
    (PrimeLocalization.under_map R P A i)⟩

include P in
theorem finite_maximals : Finite (MaximalSpectrum A) := by
  let f : MaximalSpectrum A → ι := fun q => Classical.choose (maximal_eq_map R P A q.asIdeal)
  have hf (q : MaximalSpectrum A) : q.asIdeal = (P (f q)).asIdeal.map (algebraMap R A) :=
    Classical.choose_spec (maximal_eq_map R P A q.asIdeal)
  apply Finite.of_injective f
  intro q q' h
  apply MaximalSpectrum.ext
  exact (hf q).trans ((congrArg (fun i => (P i).asIdeal.map (algebraMap R A)) h).trans (hf q').symm)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.PrimeSemilocal
