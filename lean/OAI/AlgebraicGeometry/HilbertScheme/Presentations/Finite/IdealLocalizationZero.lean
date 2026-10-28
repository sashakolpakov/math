import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Finiteness.Basic

/-! # Ideal Localization Zero -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.IdealLocalizationZero

noncomputable section

/-! A finitely generated ideal which vanishes in a localization already
vanishes after inverting a single member of the multiplicative set. -/

open scoped BigOperators

universe u v
variable {R : Type u} [CommRing R]

theorem finite_ideal_localization_zero (U : Submonoid R)
    (S : Type v) [CommRing S] [Algebra R S] [IsLocalization U S]
    (I : Ideal R) (hI : I.FG) (hz : I.map (algebraMap R S) = ⊥) :
    ∃ s : U, I.map (algebraMap R (Localization.Away s.val)) = ⊥ := by
  classical
  obtain ⟨G, hG⟩ := hI
  have hg (x : G) : ∃ s : U, s.val * x.val = 0 := by
    have hx : algebraMap R S x.val = 0 :=
      (Ideal.map_eq_bot_iff_le_ker _).mp hz (hG ▸ Ideal.subset_span x.property)
    obtain ⟨s, hs⟩ := (IsLocalization.eq_iff_exists U S).mp (hx.trans (map_zero _).symm)
    exact ⟨s, by simpa only [mul_zero] using hs⟩
  choose d hd using hg
  let s : U := ∏ x : G, d x
  refine ⟨s, (Ideal.map_eq_bot_iff_le_ker _).mpr ?_⟩
  rw [← hG]
  apply Ideal.span_le.mpr
  intro x hx
  have hdiv : (d ⟨x, hx⟩).val ∣ s.val := by
    change (d ⟨x, hx⟩).val ∣ (∏ y : G, d y : U).val
    rw [Submonoid.coe_finsetProd]
    exact Finset.dvd_prod_of_mem (fun y : G => (d y).val) (Finset.mem_univ (⟨x, hx⟩ : G))
  obtain ⟨a, ha⟩ := hdiv
  have hsx : s.val * x = 0 := by
    rw [ha, mul_right_comm, hd ⟨x, hx⟩, zero_mul]
  change algebraMap R (Localization.Away s.val) x = 0
  apply (IsLocalization.Away.algebraMap_isUnit s.val).mul_right_injective
  dsimp only
  rw [mul_zero, ← map_mul, hsx, map_zero]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.IdealLocalizationZero
