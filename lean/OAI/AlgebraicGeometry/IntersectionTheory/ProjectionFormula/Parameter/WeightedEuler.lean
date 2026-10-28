import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IsolatedParameterDimension
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MinimalPrimeFiltration

/-! # Weighted Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.WeightedEuler

noncomputable section

/-! The native Euler characteristic of an isolated parameter fiber is
the sum of orders along the nonclosed support primes, weighted by the
actual localized module lengths. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory IsLocalRing
open scoped Classical

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (M : ModuleCat.{u} R) [Module.Finite R M] (r : R)
  (hisolated : Module.support R M ∩ Module.support R (R ⧸ Ideal.span {r}) ⊆ {closedPoint R})

include hisolated

omit [IsDomain R] [IsNoetherianRing R] [Module.Finite R M] in
theorem avoid (p : PrimeSpectrum R) (hp : p ∈ Module.support R M) (hne : p ≠ closedPoint R) : r ∉ p.asIdeal := by
  intro hr
  apply hne
  apply Set.mem_singleton_iff.mp (hisolated ⟨hp, ?_⟩)
  rw [Module.support_of_algebra, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
  exact Ideal.span_le.mpr (fun a ha => (Set.mem_singleton_iff.mp ha).symm ▸ hr)

theorem exists_sum (hr : r ≠ 0) (hrm : r ∈ maximalIdeal R) :
    ∃ T : Finset (PrimeSpectrum R),
      (∀ p ∈ T, p ∈ Module.support R M ∧ p ≠ closedPoint R ∧ r ∉ p.asIdeal) ∧
      (∀ p ∈ Module.support R M, p ≠ closedPoint R → p ∉ T →
        FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal) M = 0) ∧
      Tor.Euler.euler R M (.of R (R ⧸ Ideal.span {r})) 1 =
        ∑ p ∈ T, ((FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal) M).toNat : ℚ) *
          ((Ring.ord (R ⧸ p.asIdeal) (Ideal.Quotient.mk p.asIdeal r)).toNat : ℚ) := by
  let := PrimeEuler.quotient_bound R r hr
  obtain ⟨k, q, hsupp, he, hcount⟩ := MinimalPrimeFiltration.exists_prime_sum_counts R M
    (.of R (R ⧸ Ideal.span {r})) 1 (closedPoint R) hisolated
  let U := Finset.univ.image q
  let T := U.filter (fun p => p ≠ closedPoint R)
  have hU (p : PrimeSpectrum R) (hp : p ∈ U) : p ∈ Module.support R M := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact hsupp i (MinimalPrimeFiltration.prime_mem_support R (q i))
  have hc (p : PrimeSpectrum R) (hp : p ∈ Module.support R M) (hn : p ≠ closedPoint R) :
      FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal) M =
        (Finset.univ.filter (fun i => q i = p)).card :=
    hcount p (IsolatedParameterDimension.minimal R M r hisolated hrm p hp hn)
  refine ⟨T, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨hpU, hpn⟩ := Finset.mem_filter.mp hp
    exact ⟨hU p hpU, hpn, avoid R M r hisolated p (hU p hpU) hpn⟩
  · intro p hp hn hpT
    rw [hc p hp hn]
    have hz : Finset.univ.filter (fun i => q i = p) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hpT (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
        ⟨i, Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩, hn⟩)
    rw [hz, Finset.card_empty, Nat.cast_zero]
  · have hgroup := Finset.sum_fiberwise_of_maps_to' (s := Finset.univ) (t := U) (g := q)
      (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      (fun p => Tor.Euler.euler R (.of R (R ⧸ p.asIdeal)) (.of R (R ⧸ Ideal.span {r})) 1)
    have hfilter : (∑ p ∈ T, ∑ i ∈ Finset.univ.filter (fun i => q i = p),
        Tor.Euler.euler R (.of R (R ⧸ p.asIdeal)) (.of R (R ⧸ Ideal.span {r})) 1) =
        ∑ p ∈ U, ∑ i ∈ Finset.univ.filter (fun i => q i = p),
          Tor.Euler.euler R (.of R (R ⧸ p.asIdeal)) (.of R (R ⧸ Ideal.span {r})) 1 := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro p hpU hpT
      have hp : p = closedPoint R := by
        by_contra hn
        exact hpT (Finset.mem_filter.mpr ⟨hpU, hn⟩)
      rw [hp]
      apply Finset.sum_eq_zero
      intro i _
      exact PrimeEuler.closed_euler_zero R r hr
    rw [he, ← hgroup, ← hfilter]
    apply Finset.sum_congr rfl
    intro p hp
    obtain ⟨hpU, hpn⟩ := Finset.mem_filter.mp hp
    rw [hc p (hU p hpU) hpn, ENat.toNat_natCast,
      PrimeEuler.prime_euler R r hr p (avoid R M r hisolated p (hU p hpU) hpn)]
    simp only [Finset.sum_const, nsmul_eq_mul]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.WeightedEuler
