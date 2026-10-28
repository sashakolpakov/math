import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Submodule

/-! # Idempotent Ideal Localization -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.IdempotentIdealLocalization.Constructions

/-! An idempotent ideal vanishes in every Noetherian local ring
centered on its zero locus. -/

universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R]

theorem map_eq_bot (I : Ideal R) (hI : IsIdempotentElem I) (p : PrimeSpectrum R)
    (hp : I ≤ p.asIdeal) : I.map (algebraMap R (Localization.AtPrime p.asIdeal)) = ⊥ := by
  let A := Localization.AtPrime p.asIdeal
  have hid : IsIdempotentElem (I.map (algebraMap R A)) := by
    change I.map (algebraMap R A) * I.map (algebraMap R A) = I.map (algebraMap R A)
    rw [← Ideal.map_mul, hI.eq]
  have hle : I.map (algebraMap R A) ≤ IsLocalRing.maximalIdeal A := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff A p.asIdeal r).mpr (hp hr)
  rcases (Ideal.isIdempotentElem_iff_eq_bot_or_top_of_isLocalRing _).mp hid with h | h
  · exact h
  · rw [h] at hle
    exact False.elim ((IsLocalRing.maximalIdeal.isMaximal A).ne_top (top_le_iff.mp hle))

end OAI.AlgebraicGeometry.CycleClass.Thom.IdempotentIdealLocalization.Constructions
