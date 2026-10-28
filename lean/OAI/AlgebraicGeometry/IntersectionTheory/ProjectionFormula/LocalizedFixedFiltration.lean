import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.UniversalPrimeFiltration

/-! # Localized Fixed Filtration -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizedFixedFiltration

noncomputable section

/-! Only the fixed filtration primes passing through a chosen
local point contribute to its native Tor Euler pairing. The other
quotient modules are zero after the actual flat localization. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory
open scoped TensorProduct Classical

universe u

theorem prime_euler_zero (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (p q : PrimeSpectrum R) [IsLocalization p.asIdeal.primeCompl S]
    (hq : ¬ q.asIdeal ≤ p.asIdeal) (N : ModuleCat.{u} S) (d : ℕ) :
    Tor.Euler.euler S ((ProjectionFormula.Flat.Extension.baseChange R S).obj (.of R (R ⧸ q.asIdeal))) N d = 0 := by
  have htop : q.asIdeal.map (algebraMap R S) = ⊤ := by
    apply IsLocalization.map_eq_top_of_not_subset p.asIdeal.primeCompl S
    intro h
    exact hq (fun a ha => not_not.mp (h ha))
  have hlen : Module.length S (S ⊗[R] (R ⧸ q.asIdeal)) = 0 := by
    rw [← (Ideal.qoutMapEquivTensorQout (R := R) (I := q.asIdeal) S).length_eq, htop]
    exact Module.length_eq_zero
  let : Subsingleton ((ProjectionFormula.Flat.Extension.baseChange R S).obj (.of R (R ⧸ q.asIdeal))) :=
    Module.length_eq_zero_iff.mp hlen
  exact PrimeFiltrationEuler.euler_zero_left S _ N d

theorem exists_data (R : Type u) [CommRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ (k : ℕ) (q : Fin k → PrimeSpectrum R),
      (∀ i, Module.support R (R ⧸ (q i).asIdeal) ⊆ Module.support R M) ∧
      (∀ p : PrimeSpectrum R,
        (∀ v ∈ Module.support R M, v.asIdeal ≤ p.asIdeal → v = p) →
        FiltrationBaseLength.length R (Localization.AtPrime p.asIdeal) M =
          (Finset.univ.filter (fun i => q i = p)).card) ∧
      ∀ (p : PrimeSpectrum R) (S : Type u) [CommRing S] [IsNoetherianRing S] [Algebra R S]
        [IsLocalization p.asIdeal.primeCompl S]
        (N : ModuleCat.{u} S) [Module.Finite S N] (d : ℕ) [HasProjectiveDimensionLE N d]
        (p₀ : PrimeSpectrum S),
        Module.support S ((ProjectionFormula.Flat.Extension.baseChange R S).obj M) ∩ Module.support S N ⊆ {p₀} →
        Tor.Euler.euler S ((ProjectionFormula.Flat.Extension.baseChange R S).obj M) N d =
          ∑ i ∈ Finset.univ.filter (fun i => (q i).asIdeal ≤ p.asIdeal), Tor.Euler.euler S
            ((ProjectionFormula.Flat.Extension.baseChange R S).obj (.of R (R ⧸ (q i).asIdeal))) N d := by
  obtain ⟨k, q, hsupp, hcount, he⟩ := UniversalPrimeFiltration.exists_data R M
  refine ⟨k, q, hsupp, hcount, ?_⟩
  intro p S _ _ _ _ N _ d _ p₀ hisolated
  let : Module.Flat R S := IsLocalization.flat S p.asIdeal.primeCompl
  rw [he S N d p₀ hisolated]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hi hnot
  have hq : ¬ (q i).asIdeal ≤ p.asIdeal := fun h => hnot (Finset.mem_filter.mpr ⟨hi, h⟩)
  exact prime_euler_zero R S p (q i) hq N d

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.LocalizedFixedFiltration
