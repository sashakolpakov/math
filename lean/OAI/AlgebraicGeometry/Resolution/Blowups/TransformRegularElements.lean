import OAI.AlgebraicGeometry.Resolution.Blowups.ChartFlatBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RefinementHelpers

/-! # Transform Regular Elements -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.TransformRegularElements.Construction

noncomputable section

/-! Regular sections survive every actual map used in a unit-transform tree. -/

universe u

/-- An actual étale refinement preserves non-zero-divisors, including on
disconnected rings, by flatness of the given ring map. -/
theorem etale_ringHom_preserves_regular {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Etale) (r : R) (hr : IsRegular r) : IsRegular (f r) := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.Etale R S := RingHom.etale_algebraMap.mp hf
  exact ChartFlatBaseChange.Construction.flat_algebraMap_regular r hr

/-- A blowup chart need not be flat over its source. Its actual embedding
in the denominator localization nevertheless preserves regular sections. -/
theorem blowupChart_constants_preserves_regular {R : Type u} [CommRing R]
    (I : Ideal R) (a : I) (r : R) (hr : IsRegular r) :
    IsRegular (Blowup.Charts.Construction.blowupChartConstants I a r) := by
  have hloc := ChartFlatBaseChange.Construction.flat_algebraMap_regular (S := Localization.Away a.val) r hr
  constructor
  · intro x y hxy
    apply Blowup.Charts.Construction.blowupChartToLocalization_injective I a
    apply hloc.left
    have h := congrArg (Blowup.Charts.Construction.blowupChartToLocalization I a) hxy
    simpa only [map_mul, Blowup.Charts.Construction.blowupChartToLocalization_constants] using h
  · intro x y hxy
    apply Blowup.Charts.Construction.blowupChartToLocalization_injective I a
    apply hloc.right
    have h := congrArg (Blowup.Charts.Construction.blowupChartToLocalization I a) hxy
    simpa only [map_mul, Blowup.Charts.Construction.blowupChartToLocalization_constants] using h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.TransformRegularElements.Construction
