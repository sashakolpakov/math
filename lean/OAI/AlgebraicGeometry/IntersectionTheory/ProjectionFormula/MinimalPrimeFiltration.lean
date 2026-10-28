import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FiltrationBaseLength
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SurfacePrimeEuler
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Minimal Prime Filtration -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MinimalPrimeFiltration

noncomputable section

/-! At a minimal prime of a module support, the number of occurrences
in an actual prime filtration is the native localized module length. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory
open scoped TensorProduct Classical

universe u

variable (R : Type u) [CommRing R]

theorem prime_mem_support (p : PrimeSpectrum R) : p ∈ Module.support R (R ⧸ p.asIdeal) := by
  rw [Module.mem_support_iff']
  refine ⟨1, fun a ha hz => ha ?_⟩
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change algebraMap R (R ⧸ p.asIdeal) a = 0
  simpa only [Algebra.smul_def, mul_one] using hz

theorem localized_prime_length (p q : PrimeSpectrum R) (hmin : q.asIdeal ≤ p.asIdeal → q = p) :
    FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal) (.of R (R ⧸ q.asIdeal)) =
      if q = p then 1 else 0 := by
  let A := Localization.AtPrime p.asIdeal
  change Module.length A (A ⊗[R] (R ⧸ q.asIdeal)) = _
  rw [← (Ideal.qoutMapEquivTensorQout (R := R) (I := q.asIdeal) A).length_eq]
  by_cases he : q = p
  · subst q
    rw [ite_eq_left rfl, Localization.AtPrime.map_eq_maximalIdeal, SurfacePrimeEuler.residue_quotient_length]
  · rw [ite_eq_right he]
    have htop : q.asIdeal.map (algebraMap R A) = ⊤ := by
      apply IsLocalization.map_eq_top_of_not_subset p.asIdeal.primeCompl A
      intro h
      exact he (hmin (fun a ha => not_not.mp (h ha)))
    rw [htop]
    exact Module.length_eq_zero

theorem filtration_count (M : ModuleCat.{u} R)
    (s : RelSeries {(L, K) | Submodule.IsQuotientEquivQuotientPrime (A := R) (M := M) L K})
    (h₀ : s.head = ⊥) (ht : s.last = ⊤)
    (q : Fin s.length → PrimeSpectrum R)
    (e : ∀ i : Fin s.length,
      (s i.succ ⧸ (s i.castSucc).submoduleOf (s i.succ)) ≃ₗ[R] R ⧸ (q i).asIdeal)
    (p : PrimeSpectrum R) (hmin : ∀ i, (q i).asIdeal ≤ p.asIdeal → q i = p) :
    FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal) M =
      (Finset.univ.filter (fun i => q i = p)).card := by
  let A := Localization.AtPrime p.asIdeal
  let : Module.Flat R A := IsLocalization.flat A p.asIdeal.primeCompl
  rw [FiltrationBaseLength.filtration_sum R A M s h₀ ht]
  have h (i : Fin s.length) :
      FiltrationBaseLength.length R A (.of R (s i.succ ⧸ (s i.castSucc).submoduleOf (s i.succ))) =
        if q i = p then 1 else 0 :=
    (FiltrationBaseLength.length_iso R A (e i).toModuleIso).trans
      (localized_prime_length R p (q i) (hmin i))
  simp_rw [h]
  simp

variable [IsNoetherianRing R]

theorem exists_prime_sum_counts (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
    (d : ℕ) [HasProjectiveDimensionLE N d] (p₀ : PrimeSpectrum R)
    (hisolated : Module.support R M ∩ Module.support R N ⊆ {p₀}) :
    ∃ (k : ℕ) (q : Fin k → PrimeSpectrum R),
      (∀ i, Module.support R (R ⧸ (q i).asIdeal) ⊆ Module.support R M) ∧
      Tor.Euler.euler R M N d = ∑ i : Fin k, Tor.Euler.euler R (.of R (R ⧸ (q i).asIdeal)) N d ∧
      ∀ p : PrimeSpectrum R,
        (∀ q ∈ Module.support R M, q.asIdeal ≤ p.asIdeal → q = p) →
        FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal) M =
          (Finset.univ.filter (fun i => q i = p)).card := by
  obtain ⟨s, h₀, ht⟩ := IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime R M
  choose q e using fun i => (s.step i).2
  have hsupp (i : Fin s.length) : Module.support R (R ⧸ (q i).asIdeal) ⊆ Module.support R M := by
    rw [← (e i).some.support_eq]
    exact (Module.support_subset_of_surjective ((s i.castSucc).submoduleOf (s i.succ)).mkQ (Submodule.mkQ_surjective _)).trans
      (Module.support_subset_of_injective (s i.succ).subtype (Submodule.subtype_injective _))
  refine ⟨s.length, q, hsupp, ?_, fun p hp => ?_⟩
  · rw [PrimeFiltrationEuler.filtration_sum R M N d p₀ hisolated s h₀ ht]
    apply Finset.sum_congr rfl
    intro i _
    exact PrimeFiltrationEuler.euler_iso_left R (e i).some.toModuleIso N d
  · exact filtration_count R M s h₀ ht q (fun i => (e i).some) p
      (fun i hi => hp (q i) (hsupp i (prime_mem_support R (q i))) hi)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MinimalPrimeFiltration
