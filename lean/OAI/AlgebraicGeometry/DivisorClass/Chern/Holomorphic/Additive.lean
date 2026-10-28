import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ResolutionLifts
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ConnectingResolution
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.DegreeTwoSheaf

/-! # Additive -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Additive

noncomputable section

section

/-! The original logarithmic integral Chern class is the actual exponential connecting class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf
open OAI.AlgebraicGeometry.SheafCohomology.Cech.PositiveCycleHomology.Projective.CycleHomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M] [NormalSpace M]

theorem holomorphicIntegralChernClass_eq_connecting (u : Connecting.holomorphicUnitCohomology E M) :
    ChernSheaf.holomorphicIntegralChernClass E M u = Connecting.holomorphicExponentialConnecting E M u := by
  let F := IntegralConstantSheaf.integralConstantSheaf (TopCat.of M)
  let R := injectiveResolution F
  let U := Singular.holomorphicLogCover E M u
  have hU := Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of M) U (Singular.holomorphicLogCover_covers E M u)
  have h := Cech.DegreeTwoSheaf.cechDegreeTwo_sheaf_class (X := TopCat.of M) U hU F
    (IntrinsicLogCochains.holomorphicNativeIntegerDefect E M u) (IntrinsicLogCochains.holomorphicNativeIntegerDefect_closed E M u)
    (Sheaf.BoundaryDegreeTwo.sheafSecondConnectingSection (ShortExact.holomorphicExponentialSequence_shortExact E M) R
      (CohomologyTransitions.holomorphicCohomologyRepresentative E M u))
    (Sheaf.BoundaryDegreeTwo.sheafSecondConnectingSection_closed (ShortExact.holomorphicExponentialSequence_shortExact E M) R
      (CohomologyTransitions.holomorphicCohomologyRepresentative E M u))
    (ResolutionLifts.holomorphicLogResolutionLift E M u R) (ResolutionLifts.holomorphicSecondResolutionLift E M u R)
    (ResolutionLifts.holomorphicLogResolutionLift_delta E M u R) (ResolutionLifts.holomorphicResolutionLifts_middle E M u R)
    (ResolutionLifts.holomorphicSecondResolutionLift_d E M u R)
  exact h.trans (ConnectingResolution.holomorphicExponentialConnecting_resolution E M u R).symm

variable [MetrizableSpace M] [StronglyLocallyContractibleSpace M] [LocallyPathConnectedSpace M]

theorem holomorphicFirstChernClassQ_connecting (u : Connecting.holomorphicUnitCohomology E M) :
    Rational.BettiCechSheafComparison.rationalBettiCechSheafEquiv (TopCat.of M) 1 (Singular.holomorphicFirstChernClassQ E M u) =
      Rational.HolomorphicPeriod.integralToRationalSheafCohomology M (Connecting.holomorphicExponentialConnecting E M u) := by
  rw [← holomorphicIntegralChernClass_eq_connecting]
  exact (ChernSheaf.holomorphicIntegralChernClass_rationalize E M u).symm

end

/-! Additivity of the original logarithmic Chern construction, proved through its actual connecting map. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M] [NormalSpace M]
  [MetrizableSpace M] [StronglyLocallyContractibleSpace M] [LocallyPathConnectedSpace M]

def holomorphicFirstChernClassQHom : Connecting.holomorphicUnitCohomology E M →+
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of M) 2 where
  toFun := Singular.holomorphicFirstChernClassQ E M
  map_zero' := by
    apply (Rational.BettiCechSheafComparison.rationalBettiCechSheafEquiv (TopCat.of M) 1).injective
    rw [holomorphicFirstChernClassQ_connecting, map_zero, map_zero, map_zero]
  map_add' u v := by
    apply (Rational.BettiCechSheafComparison.rationalBettiCechSheafEquiv (TopCat.of M) 1).injective
    rw [holomorphicFirstChernClassQ_connecting, map_add, map_add, map_add,
      holomorphicFirstChernClassQ_connecting, holomorphicFirstChernClassQ_connecting]

theorem holomorphicFirstChernClassQ_nsmul (N : ℕ) (u : Connecting.holomorphicUnitCohomology E M) :
    Singular.holomorphicFirstChernClassQ E M (N • u) = N • Singular.holomorphicFirstChernClassQ E M u :=
  (holomorphicFirstChernClassQHom E M).map_nsmul N u

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Additive
