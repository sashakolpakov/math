import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.MinimalPrimeFiltration

/-! # Fixed Prime Filtration -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FixedPrimeFiltration

noncomputable section

/-! One actual prime filtration is fixed before choosing the other
intersection module. It simultaneously records the minimal-prime lengths
and computes every isolated native Tor Euler pairing. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory
open scoped Classical

universe u

theorem exists_data (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ (k : ℕ) (q : Fin k → PrimeSpectrum R),
      (∀ i, Module.support R (R ⧸ (q i).asIdeal) ⊆ Module.support R M) ∧
      (∀ p : PrimeSpectrum R,
        (∀ v ∈ Module.support R M, v.asIdeal ≤ p.asIdeal → v = p) →
        FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal) M =
          (Finset.univ.filter (fun i => q i = p)).card) ∧
      ∀ (N : ModuleCat.{u} R) [Module.Finite R N] (d : ℕ) [HasProjectiveDimensionLE N d]
        (p₀ : PrimeSpectrum R), Module.support R M ∩ Module.support R N ⊆ {p₀} →
        Tor.Euler.euler R M N d =
          ∑ i : Fin k, Tor.Euler.euler R (.of R (R ⧸ (q i).asIdeal)) N d := by
  obtain ⟨s, h₀, ht⟩ := IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime R M
  choose q e using fun i => (s.step i).2
  have hsupp (i : Fin s.length) : Module.support R (R ⧸ (q i).asIdeal) ⊆ Module.support R M := by
    rw [← (e i).some.support_eq]
    exact (Module.support_subset_of_surjective ((s i.castSucc).submoduleOf (s i.succ)).mkQ
      (Submodule.mkQ_surjective _)).trans
      (Module.support_subset_of_injective (s i.succ).subtype (Submodule.subtype_injective _))
  refine ⟨s.length, q, hsupp, ?_, ?_⟩
  · intro p hp
    exact MinimalPrimeFiltration.filtration_count R M s h₀ ht q (fun i => (e i).some) p
      (fun i hi => hp (q i) (hsupp i (MinimalPrimeFiltration.prime_mem_support R (q i))) hi)
  · intro N _ d _ p₀ hisolated
    rw [PrimeFiltrationEuler.filtration_sum R M N d p₀ hisolated s h₀ ht]
    apply Finset.sum_congr rfl
    intro i _
    exact PrimeFiltrationEuler.euler_iso_left R (e i).some.toModuleIso N d

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FixedPrimeFiltration
