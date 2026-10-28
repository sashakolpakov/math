import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalLocalDenominator
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Localization.Ideal

/-! # Normal Principal Associated -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalPrincipalAssociated

noncomputable section

/-! Associated primes of a nonzero principal quotient in a normal
Noetherian domain have height one. -/

open IsLocalRing

variable (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R]

theorem colon_height_one (a b : R) (ha : a ≠ 0)
    (p : Ideal R) [p.IsPrime] (hp : p = (Ideal.span {a}).colon {b}) :
    p.height = 1 := by
  let S := Localization.AtPrime p
  let : IsIntegrallyClosed S := isIntegrallyClosed_of_isLocalization S p.primeCompl
    p.primeCompl_le_nonZeroDivisors
  have hi : Function.Injective (algebraMap R S) :=
    IsLocalization.injective S p.primeCompl_le_nonZeroDivisors
  have haS : algebraMap R S a ≠ 0 := (map_ne_zero_iff _ hi).mpr ha
  have he : (Ideal.span {a}).map (algebraMap R S) = Ideal.span {algebraMap R S a} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hbS : algebraMap R S b ∉ Ideal.span {algebraMap R S a} := by
    rw [← he, IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl]
    rintro ⟨r, hr, hrb⟩
    apply hr
    change r ∈ p
    rw [hp]
    exact Submodule.mem_colon_singleton.mpr hrb
  have hm : ∀ m ∈ maximalIdeal S, ∃ k : S,
      k * algebraMap R S a = algebraMap R S b * m := by
    intro m hm
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p S] at hm
    obtain ⟨⟨⟨r, hr⟩, s⟩, hms⟩ :=
      (IsLocalization.mem_map_algebraMap_iff p.primeCompl S).mp hm
    change m * algebraMap R S s = algebraMap R S r at hms
    have hrb : r * b ∈ Ideal.span {a} := by
      exact Submodule.mem_colon_singleton.mp (hp ▸ hr)
    obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.mp hrb
    have hs : IsUnit (algebraMap R S s) := IsLocalization.map_units S s
    refine ⟨IsLocalization.mk' S k s, ?_⟩
    apply hs.mul_right_cancel
    calc
      (IsLocalization.mk' S k s * algebraMap R S a) * algebraMap R S s =
          (IsLocalization.mk' S k s * algebraMap R S s) * algebraMap R S a := by ring
      _ = algebraMap R S k * algebraMap R S a := by rw [IsLocalization.mk'_spec]
      _ = algebraMap R S b * algebraMap R S r := by rw [← map_mul, hk, map_mul, mul_comm]
      _ = (algebraMap R S b * m) * algebraMap R S s := by rw [mul_assoc, hms]
  let : (maximalIdeal S).IsPrincipal :=
    NormalLocalDenominator.maximal_principal S _ _ haS hbS hm
  have hheight : (maximalIdeal S).height ≤ 1 := by
    apply Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (maximalIdeal S)
    simp only [Ideal.minimalPrimes_eq_subsingleton_self, Set.mem_singleton_iff]
  rw [← IsLocalization.height_under p.primeCompl, Localization.AtPrime.under_maximalIdeal]
    at hheight
  apply le_antisymm hheight
  apply Order.one_le_iff_ne_zero.mpr
  apply Ideal.height_eq_zero_iff_eq_bot.not.mpr
  intro hp₀
  have haP : a ∈ p := by
    rw [hp, Submodule.mem_colon_singleton]
    exact Ideal.mul_mem_right b _ (Ideal.subset_span (Set.mem_singleton a))
  exact ha (by simpa only [hp₀, Submodule.mem_bot] using haP)

theorem height_one (a : R) (ha : a ≠ 0) (p : Ideal R)
    (hp : IsAssociatedPrime p (R ⧸ Ideal.span {a})) : p.height = 1 := by
  obtain ⟨hprime, x, hx⟩ := isAssociatedPrime_iff.mp hp
  let := hprime
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply colon_height_one R a b ha p
  rw [hx]
  ext r
  simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  rfl

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.NormalPrincipalAssociated
