import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.IdealNeighborhood
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Uniformizer Prime Support -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.UniformizerPrimeSupport.Constructions

noncomputable section

/-!
# DegreeTwo: a local uniformizer defines its prime divisor on a neighborhood

Finite generation descends equality of the two actual ideals in the DVR
to one principal neighborhood. This gives exact support equality there.
-/

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
  (P : Ideal R) [P.IsPrime]
  [IsDomain (Localization.AtPrime P)] [IsDiscreteValuationRing (Localization.AtPrime P)]

/-- A uniformizer of the actual localization cuts out precisely the
given prime divisor on a principal neighborhood of its generic point. -/
theorem uniformizer_prime_support_neighborhood (p : R)
    (hp : Irreducible (algebraMap R (Localization.AtPrime P) p)) :
    ∃ b : R, b ∉ P ∧ ∀ Q : Ideal R, Q.IsPrime → b ∉ Q → (p ∈ Q ↔ P ≤ Q) := by
  let A := Localization.AtPrime P
  let I := Ideal.span ({p} : Set R)
  have hpP : p ∈ P := by
    by_contra h
    exact hp.not_isUnit (IsLocalization.map_units A (⟨p, h⟩ : P.primeCompl))
  have hI : I.map (algebraMap R A) = IsLocalRing.maximalIdeal A := by
    change (Ideal.span {p}).map (algebraMap R A) = _
    rw [Ideal.map_span, Set.image_singleton]
    exact ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hp).symm
  have hPI : P.map (algebraMap R A) ≤ I.map (algebraMap R A) := by
    rw [hI, Localization.AtPrime.map_eq_maximalIdeal]
  obtain ⟨b, hb⟩ := IdealNeighborhood.Constructions.exists_common_ideal_denominator P.primeCompl A I P
    (IsNoetherian.noetherian P) hPI
  refine ⟨b.val, b.property, ?_⟩
  intro Q hQ hbQ
  let : Q.IsPrime := hQ
  constructor
  · intro hpQ r hrP
    have hIQ : I ≤ Q := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpQ)
    exact (hQ.mem_or_mem (hIQ (hb r hrP))).resolve_left hbQ
  · intro hPQ
    exact hPQ hpP

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.UniformizerPrimeSupport.Constructions
