import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ConcreteDivisorNeighborhood
import OAI.AlgebraicGeometry.DivisorClass.Chern.SupportedDivisorSum
import OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneWindingComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.PrimitiveNormalWinding

/-! # Thom -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-!
# ChernClass: the original first Chern class and original divisor Thom class

The constructed native chart comparison, finite divisor sum, and actual
codimension-two removal give a global equality. Its cycle is exactly the
original rational-section divisor. The remaining universal coefficient is
the already proved integral sign, not an arbitrary rational rescaling.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X) [IsIntegral X.carrier]

/-- The actual global relative Chern class is the original supported divisor
sum, with its already proved primitive orientation coefficient. -/
theorem Line.Bundles.AlgebraicLineBundle.rationalSectionChernRelativeClass_eq_actualDivisorThom :
    L.rationalSectionChernRelativeClass = NormalWinding.normalWindingCoefficient • L.rationalSectionDivisorThomClass := by
  have h := HodgeConjecture.DegreeTwo.ConcreteDivisorNeighborhood.Constructions.rationalSectionChernRelativeClass_eq_divisorThom
    (SupportedDivisorSum.Construction.integralPresentationVariety X) L
  rw [PlaneWindingComparison.neg_windingNormalCoefficient_eq_normalWindingCoefficient] at h
  exact h

/-- The actual Chern class uses the original dimension-graded integral divisor,
rationalized by the original coefficient map. -/
theorem Line.Bundles.AlgebraicLineBundle.firstChernClassQ_eq_actualDivisorThom :
    First.firstChernClassQ X L = NormalWinding.normalWindingCoefficient •
      (SupportedDivisorSum.Construction.integralPresentationVariety X).rationalCycleClass 1
        (Finsupp.mapDomain
          (Component.Construction.integralSupportToVariety (SupportedDivisorSum.Construction.integralPresentationVariety X) 1)
          (Classes.Construction.rationalizeDivisor X L.rationalSectionIntegralDivisor)) := by
  rw [← L.rationalSectionChernRelativeClass_absolute,
    L.rationalSectionChernRelativeClass_eq_actualDivisorThom, map_smul,
    L.rationalSectionDivisorThomClass_absolute_actual]

/-- The comparison coefficient is constrained to the two primitive integral
orientations; the divisor itself is unchanged. -/
theorem Line.Bundles.AlgebraicLineBundle.firstChernClassQ_eq_divisorThom_or_neg :
    First.firstChernClassQ X L =
        (SupportedDivisorSum.Construction.integralPresentationVariety X).rationalCycleClass 1 L.rationalSectionDivisorThomCycle ∨
      First.firstChernClassQ X L =
        -((SupportedDivisorSum.Construction.integralPresentationVariety X).rationalCycleClass 1 L.rationalSectionDivisorThomCycle) := by
  have h := L.firstChernClassQ_eq_actualDivisorThom
  rw [← L.rationalSectionDivisorThomCycle_eq_actual] at h
  rcases PrimitiveNormalWinding.normalWindingCoefficient_eq_one_or_neg_one with hp | hn
  · exact Or.inl (by simpa only [hp, one_smul] using h)
  · exact Or.inr (by simpa only [hn, neg_one_smul] using h)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
