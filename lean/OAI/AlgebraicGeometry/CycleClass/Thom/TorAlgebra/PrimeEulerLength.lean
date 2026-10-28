import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.PrimeEuler
import OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedModuleLength

/-! # Prime Euler Length -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.PrimeEulerLength

noncomputable section

/-! One genuine prime filtration simultaneously computes the native
Tor Euler characteristic and every localized module length. This keeps
the multiplicities in the two calculations tied to the same factors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.Euler.Tor OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.IsolatedEuler
open OAI.AlgebraicGeometry.CycleClass.Thom.LocalizedModuleLength.Constructions

set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
  (N : ModuleCat.{u} R) [Module.Finite R N] (d : ℕ) [HasProjectiveDimensionLE N d]

theorem exists_prime_euler_localLength_sum (M : Type u)
    [AddCommGroup M] [Module R M] [Module.Finite R M] (x : PrimeSpectrum R) :
    Module.support R M ∩ Module.support R N ⊆ {x} →
    ∃ ps : List (PrimeSpectrum R),
      (∀ p ∈ ps, Module.support R (R ⧸ p.asIdeal) ⊆ Module.support R M) ∧
      Euler.Tor.euler R (ModuleCat.of R M) N d =
        (ps.map (fun p => Euler.Tor.euler R (ModuleCat.of R (R ⧸ p.asIdeal)) N d)).sum ∧
      ∀ q : PrimeSpectrum R, LocalizedModuleLength.Constructions.localLength R M q =
        (ps.map (fun p => LocalizedModuleLength.Constructions.localLength R (R ⧸ p.asIdeal) q)).sum := by
  induction ‹Module.Finite R M› using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with
  | subsingleton M =>
    intro _
    refine ⟨[], ?_, ?_, ?_⟩
    · simp only [List.not_mem_nil, false_implies, implies_true]
    · simpa only [List.map_nil, List.sum_nil] using
        IsolatedEuler.euler_subsingleton_left R (ModuleCat.of R M) N d
    · intro q
      simpa only [List.map_nil, List.sum_nil] using LocalizedModuleLength.Constructions.localLength_subsingleton (M := M) q
  | quotient M p e =>
    intro _
    refine ⟨[p], ?_, ?_, ?_⟩
    · intro q hq
      obtain rfl := List.mem_singleton.mp hq
      exact e.support_eq.ge
    · simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using
        IsolatedEuler.euler_iso_left R e.toModuleIso N d
    · intro q
      simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] using
        LocalizedModuleLength.Constructions.localLength_equiv e q
  | exact M₁ M₂ M₃ f g hf hg hfg ih₁ ih₃ =>
    intro hx
    have hs₁ := Module.support_subset_of_injective f hf
    have hs₃ := Module.support_subset_of_surjective g hg
    obtain ⟨ps, hps, he₁, hl₁⟩ := ih₁ ((Set.inter_subset_inter_left _ hs₁).trans hx)
    obtain ⟨qs, hqs, he₃, hl₃⟩ := ih₃ ((Set.inter_subset_inter_left _ hs₃).trans hx)
    let S := ShortComplex.moduleCatMk f g hfg.linearMap_comp_eq_zero
    let : Module.Finite R S.X₁ := inferInstanceAs (Module.Finite R M₁)
    let : Module.Finite R S.X₂ := inferInstanceAs (Module.Finite R M₂)
    let : Module.Finite R S.X₃ := inferInstanceAs (Module.Finite R M₃)
    have hS : S.ShortExact :=
      { exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr hfg
        mono_f := (ModuleCat.mono_iff_injective S.f).mpr hf
        epi_g := (ModuleCat.epi_iff_surjective S.g).mpr hg }
    refine ⟨ps ++ qs, ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact (hps p hp).trans hs₁
      · exact (hqs p hp).trans hs₃
    · rw [List.map_append, List.sum_append, ← he₁, ← he₃]
      exact IsolatedEuler.additivity_of_isolated_support R N d S hS x hx
    · intro q
      rw [List.map_append, List.sum_append, ← hl₁ q, ← hl₃ q]
      exact LocalizedModuleLength.Constructions.localLength_additivity f g hf hg hfg q

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.PrimeEulerLength
