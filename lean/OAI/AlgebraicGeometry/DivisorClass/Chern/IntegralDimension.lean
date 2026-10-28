import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.KrullDimension.Basic

/-! # Integral Dimension -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralDimension.Construction

/-!
# ChernClass: dimension comparisons for integral algebra extensions

These order-theoretic facts support the comparison between divisor points
and the function-field dimension grading of the geometric cycle-class map.
-/

open _root_.Order

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]

/-- Incomparability makes contraction strictly monotone on chains of prime ideals. -/
theorem integral_comap_strictMono : StrictMono (PrimeSpectrum.comap (algebraMap R S)) := by
  intro p q hpq
  exact Ideal.IsIntegral.under_lt_under hpq

/-- Integral extensions preserve the lengths of chains above a prime, by going up. -/
theorem integral_comap_coheight (p : PrimeSpectrum S) :
    coheight p = coheight (PrimeSpectrum.comap (algebraMap R S) p) := by
  apply coheight_eq_of_strictMono _ integral_comap_strictMono
  intro q r hqr
  obtain ⟨r', hle, hprime, hcomap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime r.asIdeal q.asIdeal hqr.le
  refine ⟨⟨r', hprime⟩, ?_, PrimeSpectrum.ext hcomap⟩
  apply lt_of_le_of_ne hle
  intro heq
  have he : PrimeSpectrum.comap (algebraMap R S) q = r := by
    apply PrimeSpectrum.ext
    change q.asIdeal.comap (algebraMap R S) = r.asIdeal
    rw [heq]
    exact hcomap
  exact hqr.ne he

/-- When going down is available, contraction also preserves prime height. -/
theorem integral_comap_height [Algebra.HasGoingDown R S] (p : PrimeSpectrum S) :
    height p = height (PrimeSpectrum.comap (algebraMap R S) p) := by
  apply height_eq_of_strictMono _ integral_comap_strictMono
  intro q r hrq
  let : q.asIdeal.LiesOver (q.asIdeal.under R) := ⟨rfl⟩
  obtain ⟨r', hlt, hprime, hover⟩ := Ideal.exists_ideal_lt_liesOver_of_lt
    (R := R) (S := S) (p := r.asIdeal) (q := q.asIdeal.under R) q.asIdeal hrq
  exact ⟨⟨r', hprime⟩, hlt, PrimeSpectrum.ext hover.over.symm⟩

/-- An injective integral extension preserves Krull dimension. -/
theorem integral_ringKrullDim_eq (hinj : Function.Injective (algebraMap R S)) :
    ringKrullDim S = ringKrullDim R := by
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S)) := by
    intro p
    obtain ⟨q, _, hprime, hcomap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal (⊥ : Ideal S)
      (by simpa only [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj]
        using (bot_le : (⊥ : Ideal R) ≤ p.asIdeal))
    exact ⟨⟨q, hprime⟩, PrimeSpectrum.ext hcomap⟩
  unfold ringKrullDim
  rw [krullDim_eq_iSup_coheight, krullDim_eq_iSup_coheight]
  simp_rw [integral_comap_coheight (R := R) (S := S)]
  exact hsurj.iSup_comp (fun p : PrimeSpectrum R => (coheight p : WithBot ℕ∞))

end OAI.AlgebraicGeometry.DivisorClass.Chern.IntegralDimension.Construction
