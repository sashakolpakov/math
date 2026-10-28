import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HeightOneEscape
import Mathlib.RingTheory.LocalRing.Quotient

/-! # Curve Escape -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.CurveEscape

noncomputable section

/-! A positive-dimensional noetherian local domain has a
one-dimensional prime quotient in which any fixed nonzero element survives. -/

open IsLocalRing

universe u

theorem exists_prime (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    (hd : 0 < (maximalIdeal R).height) (f : R) (hf : f ≠ 0) :
    ∃ p : PrimeSpectrum R,
      ringKrullDim (R ⧸ p.asIdeal) = 1 ∧ f ∉ p.asIdeal := by
  have hm : maximalIdeal R ≠ ⊥ := by
    intro he
    have hz : (maximalIdeal R).height = 0 := by rw [he]; simp
    rw [hz] at hd
    exact (lt_irrefl _ hd)
  obtain ⟨h, hhm, hh⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  obtain ⟨p, hp, hmax⟩ := exists_maximal_of_wellFoundedGT
    (fun p : Ideal R => p.IsPrime ∧ h * f ∉ p)
    ⟨⊥, Ideal.isPrime_bot, by simpa using mul_ne_zero hh hf⟩
  let : p.IsPrime := hp.1
  let : IsLocalRing (R ⧸ p) := IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have hhp : h ∉ p := fun he => hp.2 (p.mul_mem_right f he)
  have hfp : f ∉ p := fun he => hp.2 (p.mul_mem_left h he)
  have hhq : Ideal.Quotient.mk p h ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hhp
  have hfq : Ideal.Quotient.mk p f ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hfp
  have hqm : maximalIdeal (R ⧸ p) ≠ ⊥ := by
    intro he
    have hhmem : Ideal.Quotient.mk p h ∈ maximalIdeal (R ⧸ p) := by
      rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective]
      exact Ideal.mem_map_of_mem _ hhm
    exact hhq (by simpa only [he, Submodule.mem_bot] using hhmem)
  refine ⟨⟨p, hp.1⟩, ?_, hfp⟩
  rw [← maximalIdeal_height_eq_ringKrullDim]
  apply WithBot.coe_injective.eq_iff.mpr
  change (maximalIdeal (R ⧸ p)).height = 1
  apply le_antisymm _
    (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hqm))
  by_contra hn
  obtain ⟨q, hq, hfq'⟩ := HeightOneEscape.exists_prime (R ⧸ p) (lt_of_not_ge hn)
    (Ideal.Quotient.mk p (h * f)) (by rw [map_mul]; exact mul_ne_zero hhq hfq)
  let Q := q.asIdeal.comap (Ideal.Quotient.mk p)
  have hpQ : p ≤ Q := by
    intro a ha
    change Ideal.Quotient.mk p a ∈ q.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact Ideal.zero_mem _
  have hQ : Q.IsPrime ∧ h * f ∉ Q := ⟨q.isPrime.comap _, hfq'⟩
  have heq : Q = p := le_antisymm (hmax hQ hpQ) hpQ
  change q.asIdeal.comap (Ideal.Quotient.mk p) = p at heq
  have hq0 : q.asIdeal = ⊥ := by
    rw [← Ideal.map_comap_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective q.asIdeal,
      heq, Ideal.map_quotient_self]
  have hz : q.asIdeal.height = 0 := by rw [hq0]; simp
  rw [hz] at hq
  exact (by decide : (0 : ℕ∞) ≠ 1) hq

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Local.CurveEscape
