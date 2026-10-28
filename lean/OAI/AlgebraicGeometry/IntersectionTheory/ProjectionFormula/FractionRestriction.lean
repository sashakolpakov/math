import Mathlib.RingTheory.Localization.FractionRing

/-! # Fraction Restriction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FractionRestriction

noncomputable section

/-! Equal fractions remain equal after restriction wherever both
denominators remain nonzero. The fraction-field map need not descend. -/

theorem eq {R K L : Type*} [CommRing R] [IsDomain R] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] (φ : R →+* L)
    (a b c d : R) (hb : φ b ≠ 0) (hd : φ d ≠ 0)
    (h : algebraMap R K a / algebraMap R K b = algebraMap R K c / algebraMap R K d) :
    φ a / φ b = φ c / φ d := by
  have hb₀ : b ≠ 0 := fun hz => hb (hz ▸ map_zero φ)
  have hd₀ : d ≠ 0 := fun hz => hd (hz ▸ map_zero φ)
  have hbK := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb₀
  have hdK := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd₀
  have hc : a * d = c * b := by
    apply IsFractionRing.injective R K
    simpa only [map_mul] using (div_eq_div_iff hbK hdK).mp h
  apply (div_eq_div_iff hb hd).mpr
  simpa only [map_mul] using congrArg φ hc

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.FractionRestriction
