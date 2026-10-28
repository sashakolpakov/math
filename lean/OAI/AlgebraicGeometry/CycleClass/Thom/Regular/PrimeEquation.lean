import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.EquationDimensionDrop
import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.EquationQuotientSupport
import OAI.AlgebraicGeometry.CycleClass.Thom.Regular.EquationQuotients

/-! # Prime Equation -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Regular.PrimeEquation.Constructions

noncomputable section

/-! On a prime quotient of positive support dimension, an isolated
intersection admits a first equation regular both on the ambient ring
and on the source. The equation ideal and all local conditions persist. -/

open RingTheory.Sequence

universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  (p : PrimeSpectrum R)

theorem exists_regular_head (r : R) (rs : List R)
    (hr : IsWeaklyRegular R (r :: rs))
    (hm : ∀ x ∈ r :: rs, x ∈ IsLocalRing.maximalIdeal R)
    (hd : 0 < Module.supportDim R (R ⧸ p.asIdeal))
    (hi : PrimeSpectrum.zeroLocus (Ideal.ofList (r :: rs) : Set R) ∩
      Module.support R (R ⧸ p.asIdeal) ⊆ {IsLocalRing.closedPoint R}) :
    ∃ s : R,
      Ideal.ofList (s :: rs) = Ideal.ofList (r :: rs) ∧
      IsWeaklyRegular R (s :: rs) ∧
      (∀ x ∈ s :: rs, x ∈ IsLocalRing.maximalIdeal R) ∧
      IsSMulRegular (R ⧸ p.asIdeal) s ∧
      Module.supportDim R (QuotSMulTop s (R ⧸ p.asIdeal)) + 1 ≤
        Module.supportDim R (R ⧸ p.asIdeal) := by
  obtain ⟨t, ht, he, hreg, hav, hdim⟩ :=
    EquationDimensionDrop.Constructions.exists_regular_head_dimension_drop
      (R ⧸ p.asIdeal) R r rs hr hm hd hi
  have hp : p.asIdeal ∈ (Module.annihilator R (R ⧸ p.asIdeal)).minimalPrimes := by
    rw [Ideal.annihilator_quotient, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  have hnot : r + t ∉ p.asIdeal := hav p.asIdeal hp
  have hJ : Ideal.ofList rs ≤ IsLocalRing.maximalIdeal R :=
    Ideal.span_le.mpr (fun x hx => hm x (List.mem_cons_of_mem r hx))
  refine ⟨r + t, he, hreg, ?_, ?_, hdim⟩
  · intro x hx
    rcases List.mem_cons.mp hx with heq | hx
    · rw [heq]
      exact (IsLocalRing.maximalIdeal R).add_mem (hm r (List.mem_cons_self)) (hJ ht)
    · exact hm x (List.mem_cons_of_mem r hx)
  · apply (isSMulRegular_quotient_iff_mem_of_smul_mem p.asIdeal (r + t)).mpr
    intro x hx
    exact (p.isPrime.mem_or_mem hx).resolve_left hnot

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Regular.PrimeEquation.Constructions
