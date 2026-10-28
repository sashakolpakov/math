import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChernSheaf

/-! # Log Integral Boundary -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LogIntegralBoundary

noncomputable section

/-! The original integer logarithmic defect is the actual holomorphic Cech coboundary. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]
  {I : Type} (U : I → Opens M)
  (l : LogCech.RationalCech.LogCechCochain (TopCat.of M) U) (h : LogCech.RationalCech.ExponentialCocycle (TopCat.of M) U l)
  (hl : ∀ a, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ) ∞ (l a))

theorem holomorphicLogCech_integral_boundary :
    Abelian.CechCoordinates.abelianCechDelta (Sheaves.holomorphicFunctionSheaf E M).obj U 1 (CechForget.holomorphicCechOfLog E M U l hl) =
      Abelian.CechClasses.abelianCechCoefficient (X := TopCat.of M) U (PeriodSequence.holomorphicPeriodSheafMap E M).hom 2
        (LogIntegralSheaf.logarithmicIntegerCech (X := TopCat.of M) U l h) := by
  refine (LogObstruction.holomorphicLogCech_period_boundary E M U l h hl).trans ?_
  funext a
  apply ContMDiffMap.ext
  intro x
  change (((LogIntegralSheaf.logarithmicIntegerCech (X := TopCat.of M) U l h a x : ℤ) : ℚ) : ℂ) *
      (2 * (Real.pi : ℂ) * Complex.I) =
    (LogIntegralSheaf.logarithmicIntegerCech (X := TopCat.of M) U l h a x : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
  rw [Rat.cast_intCast]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LogIntegralBoundary
