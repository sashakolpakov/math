import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Finite.PrincipalPrimes
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-! # Height One Escape -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HeightOneEscape

noncomputable section

/-! In a noetherian local domain of dimension at least two, a
height-one prime can be chosen to avoid any prescribed nonzero element. -/

open IsLocalRing
open scoped Classical

universe u

theorem exists_prime (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    (hd : 1 < (maximalIdeal R).height) (f : R) (hf : f ≠ 0) :
    ∃ p : PrimeSpectrum R, p.asIdeal.height = 1 ∧ f ∉ p.asIdeal := by
  let T := (Finite.PrincipalPrimes.finite R f hf).toFinset
  let S : Finset (Ideal R) := insert ⊥ (T.image PrimeSpectrum.asIdeal)
  have hS (p : Ideal R) (hp : p ∈ S) : p.IsPrime ∧ p.height ≤ 1 := by
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact ⟨Ideal.isPrime_bot, by simp⟩
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      have hq' := (Finite.PrincipalPrimes.finite R f hf).mem_toFinset.mp hq
      exact ⟨q.isPrime, hq'.1.le⟩
  have hnot : ¬ (maximalIdeal R : Set R) ⊆ ⋃ p ∈ S, (p : Set R) := by
    intro h
    obtain ⟨p, hp, hmp⟩ := (Ideal.subset_union_prime (⊥ : Ideal R) (⊥ : Ideal R)
      (fun p hp _ _ => (hS p hp).1)).mp h
    exact (not_le_of_gt hd) ((Ideal.height_mono hmp).trans (hS p hp).2)
  obtain ⟨a, ham, hao⟩ := Set.not_subset.mp hnot
  have ha (p : Ideal R) (hp : p ∈ S) : a ∉ p := fun h =>
    hao (Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, h⟩⟩)
  have ha0 : a ≠ 0 := fun h => ha ⊥ (Finset.mem_insert_self _ _) (by simpa using h)
  obtain ⟨p, hp, _⟩ := Ideal.exists_minimalPrimes_le
    (show Ideal.span {a} ≤ maximalIdeal R from Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ham))
  let : p.IsPrime := hp.isPrime
  have hap : a ∈ p := hp.le (Ideal.subset_span (Set.mem_singleton a))
  have hp0 : p ≠ ⊥ := fun he => ha0 (by simpa only [he, Submodule.mem_bot] using hap)
  have hheight : p.height = 1 := le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {a}) p hp)
    (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hp0))
  refine ⟨⟨p, hp.isPrime⟩, hheight, ?_⟩
  intro hfp
  have hpT : (⟨p, hp.isPrime⟩ : PrimeSpectrum R) ∈ T :=
    (Finite.PrincipalPrimes.finite R f hf).mem_toFinset.mpr ⟨hheight, hfp⟩
  exact ha p (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨p, hp.isPrime⟩, hpT, rfl⟩)) hap

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HeightOneEscape
