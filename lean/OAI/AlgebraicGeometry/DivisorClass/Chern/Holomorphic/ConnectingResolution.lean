import OAI.AlgebraicGeometry.DivisorClass.Chern.Sheaf.SecondResolutionLifts
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CohomologyTransitions

/-! # Connecting Resolution -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ConnectingResolution

noncomputable section

/-! The actual exponential connecting class in explicit degree-two resolution coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]

theorem holomorphicExponentialConnecting_resolution (u : Connecting.holomorphicUnitCohomology E M)
    (R : InjectiveResolution (IntegralConstantSheaf.integralConstantSheaf (TopCat.of M))) :
    Connecting.holomorphicExponentialConnecting E M u =
      -Sheaf.ResolutionClasses.sheafResolutionCycleClass R 2
        (Sheaf.BoundaryDegreeTwo.sheafSecondConnectingSection (ShortExact.holomorphicExponentialSequence_shortExact E M) R
          (CohomologyTransitions.holomorphicCohomologyRepresentative E M u))
        (Sheaf.BoundaryDegreeTwo.sheafSecondConnectingSection_closed (ShortExact.holomorphicExponentialSequence_shortExact E M) R
          (CohomologyTransitions.holomorphicCohomologyRepresentative E M u)) := by
  have h := Sheaf.BoundaryDegreeTwo.sheafConnectingBoundary_degreeTwo (X := TopCat.of M)
    (ShortExact.holomorphicExponentialSequence_shortExact E M) R (CohomologyTransitions.holomorphicCohomologyRepresentative E M u)
  change (Sheaf.CohomologyLifts.sheafInjectiveCokernelBoundary (Sheaves.holomorphicUnitsSheaf E M)
    (CohomologyTransitions.holomorphicCohomologyRepresentative E M u)).comp
      (ShortExact.holomorphicExponentialSequence_shortExact E M).extClass (show 1 + 1 = 2 from rfl) = _ at h
  rw [CohomologyTransitions.holomorphicCohomologyRepresentative_spec] at h
  exact h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ConnectingResolution
