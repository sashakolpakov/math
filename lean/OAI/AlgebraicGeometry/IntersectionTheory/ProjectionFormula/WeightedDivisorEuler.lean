import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Principal.PrimeFiltration

/-! # Weighted Divisor Euler -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.WeightedDivisorEuler

noncomputable section

/-! The principal-quotient Euler characteristic over a local surface is
the sum over distinct height-one primes, weighted by their actual local orders. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory IsLocalRing
open scoped Classical

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]

theorem exists_order_sum (hdim : (maximalIdeal R).height = 2)
    (r : R) (hr : r ≠ 0) (N : ModuleCat.{u} R) [Module.Finite R N]
    (d : ℕ) [HasProjectiveDimensionLE N d]
    (hN : ∀ x : N, ∃ a : R, a ≠ 0 ∧ a • x = 0)
    (hisolated : Module.support R (QuotSMulTop r R) ∩ Module.support R N ⊆ {closedPoint R}) :
    ∃ S : Finset (PrimeSpectrum R),
      (∀ p ∈ S, p.asIdeal.height = 1 ∧ r ∈ p.asIdeal) ∧
      (∀ p : PrimeSpectrum R, p.asIdeal.height = 1 → p ∉ S →
        Ring.ord (Localization.AtPrime p.asIdeal)
          (algebraMap R (Localization.AtPrime p.asIdeal) r) = 0) ∧
      Tor.Euler.euler R (.of R (QuotSMulTop r R)) N d =
        ∑ p ∈ S, ((Ring.ord (Localization.AtPrime p.asIdeal)
          (algebraMap R (Localization.AtPrime p.asIdeal) r)).toNat : ℚ) *
          Tor.Euler.euler R (.of R (R ⧸ p.asIdeal)) N d := by
  obtain ⟨n, primes, hrp, he, hcount⟩ :=
    Principal.PrimeFiltration.exists_prime_sum_counts R r hr N d (closedPoint R) hisolated
  let T := Finset.univ.image primes
  let S := T.filter (fun p => p.asIdeal.height = 1)
  have hne (i : Fin n) : (primes i).asIdeal ≠ ⊥ := by
    intro hz
    have h := hrp i
    rw [hz, Submodule.mem_bot] at h
    exact hr h
  refine ⟨S, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨hpT, hheight⟩ := Finset.mem_filter.mp hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hpT
    exact ⟨hheight, hrp i⟩
  · intro p hp hpS
    rw [hcount p hp]
    have hf : Finset.univ.filter (fun i => primes i = p) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      apply hpS
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
        ⟨i, Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩, hp⟩
    rw [hf, Finset.card_empty, Nat.cast_zero]
  · rw [he]
    have hsum := Finset.sum_fiberwise_of_maps_to' (s := Finset.univ) (t := T)
      (g := primes) (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      (fun p => Tor.Euler.euler R (.of R (R ⧸ p.asIdeal)) N d)
    rw [← hsum]
    have hfilter : (∑ p ∈ T, ∑ i ∈ Finset.univ.filter (fun i => primes i = p),
        Tor.Euler.euler R (.of R (R ⧸ p.asIdeal)) N d) =
        ∑ p ∈ S, ∑ i ∈ Finset.univ.filter (fun i => primes i = p),
          Tor.Euler.euler R (.of R (R ⧸ p.asIdeal)) N d := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro p hpT hpS
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hpT
      have hh : (primes i).asIdeal.height ≠ 1 := by
        intro hh
        exact hpS (Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
          ⟨i, Finset.mem_univ _, rfl⟩, hh⟩)
      have hmax := (SurfacePrimeEuler.prime_height_one_or_maximal R hdim
        (primes i) (hne i)).resolve_left hh
      apply Finset.sum_eq_zero
      intro j _
      rw [hmax]
      exact SurfacePrimeEuler.maximal_quotient_euler_zero R N d hN
    rw [hfilter]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hcount p (Finset.mem_filter.mp hp).2, ENat.toNat_natCast]
    simp only [Finset.sum_const, nsmul_eq_mul]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.WeightedDivisorEuler
