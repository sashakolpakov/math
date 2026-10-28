import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.PrimeAvoidance
import OAI.AlgebraicGeometry.Divisors.LineBundles.DVRMaximalSquare
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Uniformizer Prime Avoidance -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.UniformizerPrimeAvoidance.BundleCycles

noncomputable section

/-! # LineBundleCycles: an actual localized uniformizer can avoid finitely many other primes -/

open IsLocalRing

variable {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
    (A : Type*) [CommRing A] [Algebra R A] [IsLocalization.AtPrime A p]
    [IsDomain A] [IsDiscreteValuationRing A]

theorem prime_not_le_local_maximal_square :
    ¬ p ≤ (maximalIdeal A ^ 2).comap (algebraMap R A) := by
  intro hp
  have hm : maximalIdeal A ≤ maximalIdeal A ^ 2 := by
    have hh : p.map (algebraMap R A) ≤ maximalIdeal A ^ 2 :=
      Ideal.map_le_iff_le_comap.mpr hp
    rwa [IsLocalization.AtPrime.map_eq_maximalIdeal p A] at hh
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  exact DVRMaximalSquare.BundleCycles.dvr_irreducible_not_mem_maximal_square hπ
    (hm ((IsLocalRing.mem_maximalIdeal π).mpr hπ.not_isUnit))

theorem exists_uniformizer_avoiding_primes {ι : Type*} [Finite ι]
    (P : ι → Ideal R) (hP : ∀ i, (P i).IsPrime) (hne : ∀ i, ¬ p ≤ P i) :
    ∃ a : R, Irreducible (algebraMap R A a) ∧ ∀ i, a ∉ P i := by
  obtain ⟨a, hap, ha2, haP⟩ := LineBundles.Finite.PrimeAvoidance.BundleCycles.finitePrimeAvoidance p
    ((maximalIdeal A ^ 2).comap (algebraMap R A)) P hP
    (prime_not_le_local_maximal_square p A) hne
  refine ⟨a, (DVRMaximalSquare.BundleCycles.dvr_irreducible_iff_maximal_not_square _).mpr ⟨?_, ha2⟩, haP⟩
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A p a).mpr hap

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.UniformizerPrimeAvoidance.BundleCycles
