import OAI.AlgebraicGeometry.CycleClass.Thom.SurjectiveModuleSupport
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Regular.RegularSequence

/-! # Isolated Equation Dimension -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedEquationDimension.Constructions

noncomputable section

/-! An isolated common zero of a finite equation list bounds the
local support dimension by the length of that list. This follows from
the height theorem in the actual quotient ring. -/

open RingTheory.Sequence

universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

theorem ringKrullDim_le_length (rs : List R)
    (hm : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R)
    (hi : PrimeSpectrum.zeroLocus (Ideal.ofList rs : Set R) ⊆ {IsLocalRing.closedPoint R}) :
    ringKrullDim R ≤ (rs.length : WithBot ℕ∞) := by
  classical
  have hmin : IsLocalRing.maximalIdeal R ∈ (Ideal.span (rs.toFinset : Set R)).minimalPrimes := by
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · apply Ideal.span_le.mpr
      intro r hr
      exact hm r (List.mem_toFinset.mp hr)
    · intro Q hQ _
      have he := Set.mem_singleton_iff.mp (hi (show (⟨Q, hQ.1⟩ : PrimeSpectrum R) ∈
          PrimeSpectrum.zeroLocus (Ideal.ofList rs : Set R) from by
        change Ideal.ofList rs ≤ Q
        simpa only [Ideal.ofList, List.coe_toFinset] using hQ.2))
      exact le_of_eq (congrArg PrimeSpectrum.asIdeal he).symm
  have hh := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
  have hc : (rs.toFinset.card : ℕ∞) ≤ rs.length := by exact_mod_cast List.toFinset_card_le rs
  have h := hh.trans hc
  have h' : ((IsLocalRing.maximalIdeal R).height : WithBot ℕ∞) ≤ rs.length := by exact_mod_cast h
  rwa [IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at h'

theorem quotient_supportDim_le_length (P : Ideal R) [P.IsPrime] (rs : List R)
    (hm : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R)
    (hi : PrimeSpectrum.zeroLocus (Ideal.ofList rs : Set R) ∩ Module.support R (R ⧸ P) ⊆
      {IsLocalRing.closedPoint R}) : Module.supportDim R (R ⧸ P) ≤ (rs.length : WithBot ℕ∞) := by
  let S := R ⧸ P
  let : IsLocalRing S := IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  let : IsLocalHom (algebraMap R S) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have his := SurjectiveModuleSupport.Constructions.isolated_ideal_intersection R S S
    Ideal.Quotient.mk_surjective (Ideal.ofList rs) hi
  have hm' : ∀ r ∈ rs.map (algebraMap R S), r ∈ IsLocalRing.maximalIdeal S := by
    rintro _ h
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp h
    exact map_nonunit (algebraMap R S) r (hm r hr)
  have hi' : PrimeSpectrum.zeroLocus (Ideal.ofList (rs.map (algebraMap R S)) : Set S) ⊆
      {IsLocalRing.closedPoint S} := by
    intro q hq
    apply his
    refine ⟨?_, ?_⟩
    · rwa [Ideal.map_ofList]
    · rw [Module.mem_support_iff_of_finite, Module.annihilator_eq_bot.mpr inferInstance]
      exact bot_le
  rw [Module.supportDim_quotient_eq_ringKrullDim]
  simpa only [List.length_map] using ringKrullDim_le_length S (rs.map (algebraMap R S)) hm' hi'

end

end OAI.AlgebraicGeometry.CycleClass.Thom.IsolatedEquationDimension.Constructions
