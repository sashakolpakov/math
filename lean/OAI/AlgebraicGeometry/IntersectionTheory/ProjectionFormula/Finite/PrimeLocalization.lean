import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Localization.Submodule

/-! # Prime Localization -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.PrimeLocalization

noncomputable section

/-! Localizing a normal Noetherian domain away from a finite nonempty
family of height-one primes produces a Dedekind domain. Prime avoidance
identifies every nonzero prime of the localization with one of the family. -/

universe u v

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  {ι : Type v} [Fintype ι] [Nonempty ι] (P : ι → PrimeSpectrum R)

def denominators : Submonoid R := ⨅ i, (P i).asIdeal.primeCompl

omit [IsNoetherianRing R] [Fintype ι] in
theorem denominators_le : denominators R P ≤ nonZeroDivisors R := by
  intro r hr
  apply mem_nonZeroDivisors_of_ne_zero
  intro hz
  have h := (Submonoid.mem_iInf.mp hr) (Classical.choice ‹Nonempty ι›)
  exact h (hz ▸ (P _).asIdeal.zero_mem)

variable (A : Type u) [CommRing A] [Algebra R A] [IsLocalization (denominators R P) A]

omit [IsDomain R] [IsNoetherianRing R] in
theorem under_le_one_of_primes (q : Ideal A) [q.IsPrime] :
    ∃ i, q.under R ≤ (P i).asIdeal := by
  classical
  have hd := ((IsLocalization.isPrime_iff_isPrime_disjoint (denominators R P) A q).mp
    inferInstance).2
  have hs : (q.under R : Set R) ⊆ ⋃ i ∈ (Finset.univ : Finset ι), ((P i).asIdeal : Set R) := by
    intro r hr
    by_contra hn
    have hm : r ∈ denominators R P := by
      apply Submonoid.mem_iInf.mpr
      intro i hi
      exact hn (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_univ i, hi⟩⟩)
    exact Set.disjoint_left.mp hd hm hr
  obtain ⟨i, _, hi⟩ := (Ideal.subset_union_prime (Classical.choice ‹Nonempty ι›)
    (Classical.choice ‹Nonempty ι›) (fun i _ _ _ => (P i).isPrime)).mp hs
  exact ⟨i, hi⟩

theorem under_eq_one_of_primes (hP : ∀ i, (P i).asIdeal.height = 1)
    (q : Ideal A) [q.IsPrime] (hq : q ≠ ⊥) : ∃ i, q.under R = (P i).asIdeal := by
  obtain ⟨i, hi⟩ := under_le_one_of_primes R P A q
  have hn : q.under R ≠ ⊥ :=
    (IsLocalization.bot_lt_under_prime (denominators R P) A (denominators_le R P) q hq).ne'
  refine ⟨i, (q.under R).eq_of_le_of_height_le hi ?_⟩
  rw [hP]
  exact Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hn)

theorem nonzero_prime_isMaximal (hP : ∀ i, (P i).asIdeal.height = 1)
    (q : Ideal A) [q.IsPrime] (hq : q ≠ ⊥) : q.IsMaximal := by
  obtain ⟨N, hN, hqN⟩ := q.exists_le_maximal (Ideal.IsPrime.ne_top inferInstance)
  let : N.IsMaximal := hN
  have hN0 : N ≠ ⊥ := fun h => hq (bot_unique (hqN.trans_eq h))
  obtain ⟨i, hi⟩ := under_eq_one_of_primes R P A hP q hq
  obtain ⟨j, hj⟩ := under_eq_one_of_primes R P A hP N hN0
  have hle : (P i).asIdeal ≤ (P j).asIdeal := by
    rw [← hi, ← hj]
    exact Ideal.comap_mono hqN
  have he : (P i).asIdeal = (P j).asIdeal :=
    (P i).asIdeal.eq_of_le_of_height_le hle (by rw [hP, hP])
  have hqeq : q = N := (IsLocalization.orderEmbedding (denominators R P) A).injective
    (hi.trans (he.trans hj.symm))
  exact hqeq ▸ hN

theorem dedekind [IsIntegrallyClosed R] (hP : ∀ i, (P i).asIdeal.height = 1) :
    IsDedekindDomain A := by
  let : IsDomain A := IsLocalization.isDomain_of_le_nonZeroDivisors A (denominators_le R P)
  let : IsNoetherianRing A := IsLocalization.isNoetherianRing (denominators R P) A inferInstance
  let : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A
    (denominators R P) (denominators_le R P)
  let : Ring.DimensionLEOne A := ⟨fun hq hp =>
    @nonzero_prime_isMaximal R _ _ _ ι _ _ P A _ _ _ hP _ hp hq⟩
  exact
    { toIsDomain := inferInstance
      toIsDedekindRing :=
        { toIsNoetherian := inferInstance
          toDimensionLEOne := inferInstance
          toIsIntegralClosure := inferInstance } }

omit [IsDomain R] [IsNoetherianRing R] [Fintype ι] [Nonempty ι] in
theorem disjoint_denominators (i : ι) :
    Disjoint (denominators R P : Set R) ((P i).asIdeal : Set R) := by
  exact Set.disjoint_left.mpr (fun _ hr hp => (Submonoid.mem_iInf.mp hr i) hp)

omit [IsDomain R] [IsNoetherianRing R] [Fintype ι] [Nonempty ι] in
theorem under_map (i : ι) :
    (Ideal.map (algebraMap R A) (P i).asIdeal).under R = (P i).asIdeal :=
  IsLocalization.under_map_of_isPrime_disjoint (denominators R P) A
    (P i).isPrime (disjoint_denominators R P i)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.PrimeLocalization
