import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.PrimeFiltrationMultiplicity

/-! # Prime Filtration -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.PrimeFiltration

noncomputable section

/-! A single actual prime filtration simultaneously computes the native
Tor Euler characteristic and the local multiplicities of a principal divisor. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory
open scoped TensorProduct Pointwise Classical

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]

omit [IsDomain R] [IsNoetherianRing R] in
theorem localized_principal_length (r : R) (p : PrimeSpectrum R) :
    FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal) (.of R (QuotSMulTop r R)) =
      Ring.ord (Localization.AtPrime p.asIdeal) (algebraMap R (Localization.AtPrime p.asIdeal) r) := by
  let A := Localization.AtPrime p.asIdeal
  have hI : (r • (⊤ : Submodule R R) : Ideal R) = Ideal.span {r} := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  change Module.length A (A ⊗[R] (R ⧸ (r • (⊤ : Submodule R R)))) = _
  rw [hI, ← (Ideal.qoutMapEquivTensorQout (R := R) (I := Ideal.span {r}) A).length_eq,
    Ideal.map_span, Set.image_singleton]
  rfl

theorem exists_prime_sum_counts (r : R) (hr : r ≠ 0) (N : ModuleCat.{u} R)
    [Module.Finite R N] (d : ℕ) [HasProjectiveDimensionLE N d] (p₀ : PrimeSpectrum R)
    (hisolated : Module.support R (QuotSMulTop r R) ∩ Module.support R N ⊆ {p₀}) :
    ∃ (n : ℕ) (primes : Fin n → PrimeSpectrum R),
      (∀ i, r ∈ (primes i).asIdeal) ∧
      Tor.Euler.euler R (.of R (QuotSMulTop r R)) N d =
        ∑ i : Fin n, Tor.Euler.euler R (.of R (R ⧸ (primes i).asIdeal)) N d ∧
      ∀ p : PrimeSpectrum R, p.asIdeal.height = 1 →
        Ring.ord (Localization.AtPrime p.asIdeal) (algebraMap R (Localization.AtPrime p.asIdeal) r) =
          (Finset.univ.filter (fun i => primes i = p)).card := by
  let M := ModuleCat.of R (QuotSMulTop r R)
  obtain ⟨s, h₀, ht⟩ := IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime R M
  choose primes e using fun i => (s.step i).2
  have hsupp (i : Fin s.length) : Module.support R (R ⧸ (primes i).asIdeal) ⊆ Module.support R M := by
    have h₁ := Module.support_subset_of_surjective
      ((s i.castSucc).submoduleOf (s i.succ)).mkQ (Submodule.mkQ_surjective _)
    have h₂ := Module.support_subset_of_injective (s i.succ).subtype (Submodule.subtype_injective _)
    rw [← (e i).some.support_eq]
    exact h₁.trans h₂
  have hrp (i : Fin s.length) : r ∈ (primes i).asIdeal := by
    have hp : primes i ∈ Module.support R (R ⧸ (primes i).asIdeal) := by
      rw [Module.mem_support_iff']
      refine ⟨1, fun a ha hz => ha ?_⟩
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change algebraMap R (R ⧸ (primes i).asIdeal) a = 0
      simpa only [Algebra.smul_def, mul_one] using hz
    have h := hsupp i hp
    change primes i ∈ Module.support R (QuotSMulTop r R) at h
    rw [Module.support_quotSMulTop] at h
    exact h.2 (Set.mem_singleton r)
  have hne (i : Fin s.length) : (primes i).asIdeal ≠ ⊥ := by
    intro h
    have hmem := hrp i
    rw [h, Submodule.mem_bot] at hmem
    exact hr hmem
  refine ⟨s.length, primes, hrp, ?_, fun p hp => ?_⟩
  · rw [PrimeFiltrationEuler.filtration_sum R M N d p₀ hisolated s h₀ ht]
    apply Finset.sum_congr rfl
    intro i _
    exact PrimeFiltrationEuler.euler_iso_left R (e i).some.toModuleIso N d
  · rw [← localized_principal_length R r p]
    exact PrimeFiltrationMultiplicity.filtration_count R M s h₀ ht primes
      (fun i => (e i).some) hne p hp

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.PrimeFiltration
