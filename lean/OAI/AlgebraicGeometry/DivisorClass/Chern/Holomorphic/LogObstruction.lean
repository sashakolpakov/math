import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CechForget
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.SheafBoundaries

/-! # Log Obstruction -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LogObstruction

noncomputable section

/-! The actual holomorphic logarithmic coboundary kills the rational period obstruction. -/

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

theorem holomorphicLogCech_period_boundary :
    Abelian.CechCoordinates.abelianCechDelta (Sheaves.holomorphicFunctionSheaf E M).obj U 1
      (CechForget.holomorphicCechOfLog E M U l hl) =
        Abelian.CechClasses.abelianCechCoefficient (X := TopCat.of M) U (Rational.HolomorphicPeriod.holomorphicRationalPeriodSheafMap E M).hom 2
          (LogCech.RationalCech.logDefectCech (TopCat.of M) U l h) := by
  apply CechForget.holomorphicCechForget_injective E M U 2
  rw [CechForget.holomorphicCechForget_delta, CechForget.holomorphicCechOfLog_forget, CechForget.holomorphicCechForget_period]
  exact (LogCech.RationalCech.periodMap_logDefectCech (TopCat.of M) U l h).symm

include hl in
theorem holomorphicLogCech_sheaf_obstruction (hU : ⨆ i, U i = ⊤) :
    Rational.HolomorphicPeriod.rationalHolomorphicObstruction E M
      (IntegralCechSheaf.rationalCechSheafClass (X := TopCat.of M) U hU 1 (LogCech.RationalCech.logDefectCech (TopCat.of M) U l h)
        (LogCech.RationalCech.logDefectCech_closed (TopCat.of M) U l h)) = 0 := by
  change CategoryTheory.Sheaf.H.map (Rational.HolomorphicPeriod.holomorphicRationalPeriodSheafMap E M) 2
    (Abelian.CechClasses.abelianCechSheafClass (X := TopCat.of M) U (Rational.HolomorphicPeriod.rationalConstantAbelianSheaf (TopCat.of M)) hU 1
      (LogCech.RationalCech.logDefectCech (TopCat.of M) U l h) _) = 0
  rw [Abelian.CechClasses.abelianCechSheafClass_naturality (X := TopCat.of M)]
  exact Cech.SheafBoundaries.abelianCechSheafClass_eq_zero_of_boundary (X := TopCat.of M) U (Sheaves.holomorphicFunctionSheaf E M) hU 1 _ _
    (CechForget.holomorphicCechOfLog E M U l hl) (holomorphicLogCech_period_boundary E M U l h hl)

variable [MetrizableSpace M] [StronglyLocallyContractibleSpace M] [LocallyPathConnectedSpace M]

include hl in
theorem holomorphicLogCech_betti_obstruction (hU : ∀ x : M, ∃ i, x ∈ U i) :
    Rational.HolomorphicPeriod.rationalHolomorphicObstruction E M
      (Rational.BettiCechSheafComparison.rationalBettiCechSheafEquiv (TopCat.of M) 1
        (LogCech.RationalCech.logarithmicSingularClass (TopCat.of M) U hU l h)) = 0 := by
  have hc := Cech.BettiSheafCompatibility.rationalCechSheafClass_eq_betti (X := TopCat.of M) U hU
    (Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of M) U hU) (LogCech.RationalCech.logDefectCocycle (TopCat.of M) U l h)
  change _ = Rational.BettiCechSheafComparison.rationalBettiCechSheafEquiv (TopCat.of M) 1
    (LogCech.RationalCech.logarithmicSingularClass (TopCat.of M) U hU l h) at hc
  rw [← hc]
  exact holomorphicLogCech_sheaf_obstruction E M U l h hl (Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of M) U hU)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LogObstruction
