import OAI.AlgebraicGeometry.DivisorClass.Chern.ComponentThomComparison
import OAI.AlgebraicGeometry.DivisorClass.Chern.NormalGeometricTrace

/-! # Orientation Condition -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-!
# ChernClass: the exact orientation condition in the original divisor comparison

The signed Thom comparison is already proved for the same original divisor.
Its sign disappears exactly when the existing equator coordinate is positive
or the resulting divisor class vanishes. No normalization is replaced.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem OrientationCondition.normalWindingCoefficient_smul_eq_self_iff
    {M : Type*} [AddCommGroup M] [Module ℚ M] (v : M) :
    NormalWinding.normalWindingCoefficient • v = v ↔ CircleEquatorOrientation.chosenCircleEquatorSign = 1 ∨ v = 0 := by
  constructor
  · intro h
    have hz : (NormalWinding.normalWindingCoefficient - 1) • v = 0 := by
      rw [sub_smul, one_smul, h, sub_self]
    rcases smul_eq_zero.mp hz with hq | hv
    · exact Or.inl (NormalGeometricTrace.normalWindingCoefficient_eq_one_iff_equator_positive.mp (sub_eq_zero.mp hq))
    · exact Or.inr hv
  · rintro (hq | rfl)
    · rw [NormalGeometricTrace.normalWindingCoefficient_eq_one_iff_equator_positive.mpr hq, one_smul]
    · exact smul_zero _

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X) [IsIntegral X.carrier]

theorem Line.Bundles.AlgebraicLineBundle.firstChernClassQ_eq_originalThom_iff :
    First.firstChernClassQ X L =
        (SupportedDivisorSum.Construction.integralPresentationVariety X).rationalCycleClass 1 L.rationalSectionDivisorThomCycle ↔
      CircleEquatorOrientation.chosenCircleEquatorSign = 1 ∨
        (SupportedDivisorSum.Construction.integralPresentationVariety X).rationalCycleClass 1 L.rationalSectionDivisorThomCycle = 0 := by
  rw [L.firstChernClassQ_eq_actualDivisorThom, ← L.rationalSectionDivisorThomCycle_eq_actual]
  exact OrientationCondition.normalWindingCoefficient_smul_eq_self_iff _

/-- If the original Thom and geometric classes of this original divisor
are identified, the remaining exact Chern equality still has this explicit
orientation condition. The trace identification is a stated hypothesis here. -/
theorem Line.Bundles.AlgebraicLineBundle.firstChernClassQ_eq_algebraicDivisorClass_iff_orientation
    (htrace : (SupportedDivisorSum.Construction.integralPresentationVariety X).rationalCycleClass 1
      L.rationalSectionDivisorThomCycle = L.algebraicDivisorClass) :
    First.firstChernClassQ X L = L.algebraicDivisorClass ↔
      CircleEquatorOrientation.chosenCircleEquatorSign = 1 ∨ L.algebraicDivisorClass = 0 := by
  rw [← htrace]
  exact L.firstChernClassQ_eq_originalThom_iff

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
