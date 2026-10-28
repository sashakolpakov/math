import OAI.AlgebraicGeometry.CycleClass.Thom.SemilocalLength
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-! # Branch Order -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.BranchOrder.Constructions

noncomputable section

/-! Prime-factor multiplicities on a normal curve are the actual local
orders. This identifies the weights in the semilocal length formula with
the `Ring.ord` used in geometric principal divisors. -/

open UniqueFactorizationMonoid
open scoped Classical BigOperators

open IsDedekindDomain

variable {S : Type*} [CommRing S] [IsDedekindDomain S]

theorem finite_heightOneSpectrum (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S] :
    Finite (HeightOneSpectrum S) := by
  let : Finite {P : Ideal S // P.IsMaximal} :=
    (SemilocalPID.Constructions.finite_maximalIdeals R S).to_subtype
  apply Finite.of_injective
    (fun P : HeightOneSpectrum S =>
      (⟨P.asIdeal, inferInstance⟩ : {P : Ideal S // P.IsMaximal}))
  intro P Q h
  exact HeightOneSpectrum.ext (congrArg Subtype.val h)

theorem localizedIdeal_eq_pow (P : Ideal S) [P.IsPrime] (hP : P ≠ ⊥)
    (I : Ideal S) (hI : I ≠ ⊥) :
    I.map (algebraMap S (Localization.AtPrime P)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ (normalizedFactors I).count P := by
  let : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP
  obtain ⟨Q, hPQ, hIQ⟩ := Ideal.eq_prime_pow_mul_coprime hI P
  have hQ : ¬ Q ≤ P := by
    intro hle
    exact Ideal.IsMaximal.ne_top (inferInstanceAs P.IsMaximal)
      ((sup_eq_left.mpr hle).symm.trans hPQ)
  nth_rw 1 [hIQ]
  rw [Ideal.map_mul, Ideal.map_pow,
    Localization.AtPrime.map_eq_maximalIdeal,
    IsLocalization.AtPrime.map_eq_top_of_not_le (Localization.AtPrime P) hQ, Ideal.mul_top]

/-- The local quotient length is precisely the multiplicity of the prime
in the factorization of the principal ideal. -/
theorem ord_eq_count (P : Ideal S) [P.IsPrime] (hP : P ≠ ⊥)
    (a : S) (ha : a ≠ 0) :
    Ring.ord (Localization.AtPrime P) (algebraMap S (Localization.AtPrime P) a) =
      ((normalizedFactors (Ideal.span ({a} : Set S))).count P : ℕ∞) := by
  let : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hP _
  have h := localizedIdeal_eq_pow P hP (Ideal.span {a})
    (fun h => ha (Ideal.span_singleton_eq_bot.mp h))
  rw [Ideal.map_span, Set.image_singleton] at h
  change Module.length (Localization.AtPrime P)
    ((Localization.AtPrime P) ⧸ Ideal.span {algebraMap S (Localization.AtPrime P) a}) = _
  rw [h, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]

/-- Quotient length decomposed into its distinct source branches, with the
order of each branch counted once and weighted by its residue-field degree. -/
theorem length_eq_sum_weighted_counts
    (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R S] [Module.Finite R S]
    (a : S) (ha : a ≠ 0) :
    Module.length R (S ⧸ Ideal.span {a}) =
      ∑ P ∈ (normalizedFactors (Ideal.span ({a} : Set S))).toFinset,
        (P.inertiaDeg R : ℕ∞) *
          ((normalizedFactors (Ideal.span ({a} : Set S))).count P : ℕ∞) := by
  rw [SemilocalLength.Constructions.length_quotient_eq_sum _
    (fun h => ha (Ideal.span_singleton_eq_bot.mp h))]
  have h := Finset.sum_multiset_map_count
    (normalizedFactors (Ideal.span ({a} : Set S))) (fun P => P.inertiaDeg R)
  rw [h, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro P _
  simp only [nsmul_eq_mul, Nat.cast_id, Nat.cast_mul, mul_comm]

/-- The branch formula written using the actual local orders, with each
source prime included exactly once. -/
theorem length_eq_sum_local_orders
    (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R S] [Module.Finite R S]
    [Fintype (HeightOneSpectrum S)] (a : S) (ha : a ≠ 0) :
    Module.length R (S ⧸ Ideal.span {a}) =
      ∑ P : HeightOneSpectrum S, (P.asIdeal.inertiaDeg R : ℕ∞) *
        Ring.ord (Localization.AtPrime P.asIdeal)
          (algebraMap S (Localization.AtPrime P.asIdeal) a) := by
  simp_rw [ord_eq_count _ (HeightOneSpectrum.ne_bot _) a ha]
  rw [length_eq_sum_weighted_counts R a ha]
  symm
  refine Finset.sum_bij_ne_zero (fun P _ _ => P.asIdeal) ?_ ?_ ?_ ?_
  · intro P _ hP
    by_contra hnot
    have hz : (normalizedFactors (Ideal.span ({a} : Set S))).count P.asIdeal = 0 :=
      Multiset.count_eq_zero.mpr (fun h => hnot (Multiset.mem_toFinset.mpr h))
    exact hP (by rw [hz, Nat.cast_zero, mul_zero])
  · intro P _ _ Q _ _ h
    exact HeightOneSpectrum.ext h
  · intro P hP hn
    have hp := prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)
    refine ⟨⟨P, Ideal.isPrime_of_prime hp, hp.ne_zero⟩, Finset.mem_univ _, ?_, rfl⟩
    exact hn
  · intro P _ _
    rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.BranchOrder.Constructions
