import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalPrincipalAssociated
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.FactorialTwo
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-! # Normal Divisibility -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalDivisibility

/-! Divisibility in a normal Noetherian domain is detected at the
height-one primes. In particular, equal local orders imply association. -/

variable (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R]

theorem of_localizations (a b : R) (ha : a ≠ 0)
    (h : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      algebraMap R (Localization.AtPrime p) a ∣ algebraMap R (Localization.AtPrime p) b) :
    a ∣ b := by
  by_contra hn
  have hb : b ∉ Ideal.span {a} := by simpa only [Ideal.mem_span_singleton] using hn
  have hx : Ideal.Quotient.mk (Ideal.span {a}) b ≠ 0 :=
    Ideal.Quotient.eq_zero_iff_mem.not.mpr hb
  obtain ⟨p, hp, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R _ hx
  let := hp.isPrime
  have hh := NormalPrincipalAssociated.height_one R a ha p hp
  have hmem : algebraMap R (Localization.AtPrime p) b ∈
      (Ideal.span {a}).map (algebraMap R (Localization.AtPrime p)) := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    exact h p hh
  obtain ⟨s, hs, hsb⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl _ _ _).mp hmem
  apply hs
  apply hle
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
  change Ideal.Quotient.mk (Ideal.span {a}) (s * b) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hsb

theorem associated_of_localizations (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      Associated (algebraMap R (Localization.AtPrime p) a)
        (algebraMap R (Localization.AtPrime p) b)) : Associated a b := by
  apply associated_of_dvd_dvd
  · exact of_localizations R a b ha (fun p _ hp => (h p hp).dvd)
  · exact of_localizations R b a hb (fun p _ hp => (h p hp).symm.dvd)

theorem localization_dvr (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  let S := Localization.AtPrime p
  let : IsIntegrallyClosed S := isIntegrallyClosed_of_isLocalization S p.primeCompl
    p.primeCompl_le_nonZeroDivisors
  have hm : (IsLocalRing.maximalIdeal S).height = 1 := by
    rw [← IsLocalization.height_under p.primeCompl,
      Localization.AtPrime.under_maximalIdeal, hp]
  let : IsDedekindDomain S := Local.FactorialTwo.dedekind_of_maximal_height_one S hm
  have hn : ¬ IsField S := by
    intro hf
    have hz := IsLocalRing.isField_iff_maximalIdeal_eq.mp hf
    rw [hz, Ideal.height_bot] at hm
    exact zero_ne_one hm
  exact ((IsDiscreteValuationRing.TFAE S hn).out 3 1 rfl rfl).mp inferInstance

theorem associated_of_orders (a b : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      Ring.ord (Localization.AtPrime p) (algebraMap R (Localization.AtPrime p) a) =
        Ring.ord (Localization.AtPrime p) (algebraMap R (Localization.AtPrime p) b)) :
    Associated a b := by
  apply associated_of_localizations R a b ha hb
  intro p hprime hp
  let := localization_dvr R p hp
  exact (Ring.ord_eq_iff_associated _ _).mp (h p hp)

theorem isUnit_of_orders (a : R) (ha : a ≠ 0)
    (h : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      Ring.ord (Localization.AtPrime p) (algebraMap R (Localization.AtPrime p) a) = 0) :
    IsUnit a := by
  apply associated_one_iff_isUnit.mp
  apply associated_of_orders R a 1 ha one_ne_zero
  intro p hprime hp
  simpa only [map_one, Ring.ord_one] using h p hp

end AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalDivisibility

namespace AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalDivisibility.PrimePrincipalFromOrders

/-! The characteristic height-one orders determine a prime ideal as the
principal ideal of the element realizing them in a normal domain. -/

open scoped Classical

variable (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

theorem span_eq (p : Ideal R) [p.IsPrime] (hp : p.height = 1) (r : R) (hr : r ≠ 0)
    (ho : ∀ (q : Ideal R) [q.IsPrime], q.height = 1 →
      Ring.ord (Localization.AtPrime q) (algebraMap R (Localization.AtPrime q) r) =
        if q = p then 1 else 0) : p = Ideal.span {r} := by
  have hrp : r ∈ p := by
    by_contra hn
    have hu : IsUnit (algebraMap R (Localization.AtPrime p) r) :=
      IsLocalization.map_units (Localization.AtPrime p) (⟨r, hn⟩ : p.primeCompl)
    have h := ho p hp
    rw [ite_eq_left rfl, Ring.ord_of_isUnit hu] at h
    exact zero_ne_one h
  apply le_antisymm
  · intro x hx
    apply Ideal.mem_span_singleton.mpr
    apply of_localizations R r x hr
    intro q hprime hq
    let S := Localization.AtPrime q
    let : IsDiscreteValuationRing S := localization_dvr R q hq
    apply IsDiscreteValuationRing.addVal_le_iff_dvd.mp
    rw [← Ring.ord_eq_addVal, ← Ring.ord_eq_addVal, ho q hq]
    by_cases he : q = p
    · subst q
      rw [ite_eq_left rfl]
      apply Order.one_le_iff_ne_zero.mpr
      intro hz
      have hu : IsUnit (algebraMap R (Localization.AtPrime p) x) :=
        IsDiscreteValuationRing.addVal_eq_zero_iff.mp (by simpa only [Ring.ord_eq_addVal] using hz)
      have hm : algebraMap R (Localization.AtPrime p) x ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal]
        exact Ideal.mem_map_of_mem _ hx
      exact (IsLocalRing.notMem_maximalIdeal.mpr hu) hm
    · rw [ite_eq_right he]
      exact zero_le
  · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hrp)

end AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalDivisibility.PrimePrincipalFromOrders

end

end OAI
