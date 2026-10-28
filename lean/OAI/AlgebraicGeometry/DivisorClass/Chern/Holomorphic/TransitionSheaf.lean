import OAI.AlgebraicGeometry.DivisorClass.Chern.TransitionIntrinsicResolution
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CohomologyTransitions

/-! # Transition Sheaf -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.TransitionSheaf

noncomputable section

/-! The original holomorphic-unit transition cocycle has exactly its original H1 class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M]

def holomorphicTransitionCech (u : Connecting.holomorphicUnitCohomology E M) :
    Abelian.CechCoordinates.AbelianCechCochain (Sheaves.holomorphicUnitsSheaf E M).obj (CohomologyTransitions.holomorphicCohomologyDomain E M u) 1 :=
  (CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).transitionCech
    (Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence_shortExact (Sheaves.holomorphicUnitsSheaf E M))

theorem holomorphicTransitionCech_closed (u : Connecting.holomorphicUnitCohomology E M) :
    Abelian.CechCoordinates.abelianCechDelta (Sheaves.holomorphicUnitsSheaf E M).obj (CohomologyTransitions.holomorphicCohomologyDomain E M u) 1
      (holomorphicTransitionCech E M u) = 0 :=
  (CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).transitionCech_closed
    (Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence_shortExact (Sheaves.holomorphicUnitsSheaf E M))

theorem holomorphicTransitionCech_sheaf_class (u : Connecting.holomorphicUnitCohomology E M) :
    Abelian.CechClasses.abelianCechSheafClass (X := TopCat.of M) (CohomologyTransitions.holomorphicCohomologyDomain E M u)
      (Sheaves.holomorphicUnitsSheaf E M) (CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).iSup_domain 0
      (holomorphicTransitionCech E M u) (holomorphicTransitionCech_closed E M u) = u := by
  have h := Sheaf.CohomologyLifts.SheafLocalLiftCover.transitionCech_sheaf_class (X := TopCat.of M)
    (Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence_shortExact (Sheaves.holomorphicUnitsSheaf E M))
    (CohomologyTransitions.holomorphicCohomologyLocalLifts E M u)
  change Abelian.CechClasses.abelianCechSheafClass (X := TopCat.of M)
    (CohomologyTransitions.holomorphicCohomologyDomain E M u) (Sheaves.holomorphicUnitsSheaf E M)
    (CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).iSup_domain 0 (holomorphicTransitionCech E M u)
    (holomorphicTransitionCech_closed E M u) =
      Sheaf.CohomologyLifts.sheafInjectiveCokernelBoundary (Sheaves.holomorphicUnitsSheaf E M)
        (CohomologyTransitions.holomorphicCohomologyRepresentative E M u) at h
  exact h.trans (CohomologyTransitions.holomorphicCohomologyRepresentative_spec E M u)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.TransitionSheaf
