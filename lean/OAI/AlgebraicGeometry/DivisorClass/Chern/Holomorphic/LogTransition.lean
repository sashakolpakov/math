import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.ClassRefinement
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.TransitionSheaf
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ChernSheaf

/-! # Log Transition -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LogTransition

noncomputable section

/-! The original chosen logarithms exponentiate to a refined cocycle with the original unit class. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M] [NormalSpace M]

def holomorphicLogTransitionCech (u : Connecting.holomorphicUnitCohomology E M) :
    Abelian.CechCoordinates.AbelianCechCochain (Sheaves.holomorphicUnitsSheaf E M).obj (Singular.holomorphicLogCover E M u) 1 :=
  Cech.AbelianRefinement.abelianCechRefinementMap (X := TopCat.of M) (CohomologyTransitions.holomorphicCohomologyDomain E M u)
    (Singular.holomorphicLogCover E M u) (fun i => i.2.val) (Singular.holomorphicLogCover_subset E M u)
    (Sheaves.holomorphicUnitsSheaf E M).obj 1 (TransitionSheaf.holomorphicTransitionCech E M u)

theorem holomorphicLogTransitionCech_closed (u : Connecting.holomorphicUnitCohomology E M) :
    Abelian.CechCoordinates.abelianCechDelta (Sheaves.holomorphicUnitsSheaf E M).obj (Singular.holomorphicLogCover E M u) 1
      (holomorphicLogTransitionCech E M u) = 0 :=
  Cech.ClassRefinement.abelianCechRefinementMap_closed (X := TopCat.of M) (CohomologyTransitions.holomorphicCohomologyDomain E M u)
    (Singular.holomorphicLogCover E M u) (fun i => i.2.val) (Singular.holomorphicLogCover_subset E M u)
    (Sheaves.holomorphicUnitsSheaf E M).obj 1 (TransitionSheaf.holomorphicTransitionCech E M u)
    (TransitionSheaf.holomorphicTransitionCech_closed E M u)

theorem holomorphicLogTransitionCech_sheaf_class (u : Connecting.holomorphicUnitCohomology E M) :
    Abelian.CechClasses.abelianCechSheafClass (X := TopCat.of M) (Singular.holomorphicLogCover E M u)
      (Sheaves.holomorphicUnitsSheaf E M)
      (Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of M) (Singular.holomorphicLogCover E M u) (Singular.holomorphicLogCover_covers E M u))
      0 (holomorphicLogTransitionCech E M u) (holomorphicLogTransitionCech_closed E M u) = u := by
  have h := Cech.ClassRefinement.abelianCechSheafClass_refinement (X := TopCat.of M)
    (CohomologyTransitions.holomorphicCohomologyDomain E M u) (Singular.holomorphicLogCover E M u) (fun i => i.2.val)
    (Singular.holomorphicLogCover_subset E M u) (Sheaves.holomorphicUnitsSheaf E M)
    (CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).iSup_domain
    (Cech.BettiSheafCompatibility.cechCover_iSup_eq_top (X := TopCat.of M) (Singular.holomorphicLogCover E M u) (Singular.holomorphicLogCover_covers E M u))
    0 (TransitionSheaf.holomorphicTransitionCech E M u) (TransitionSheaf.holomorphicTransitionCech_closed E M u)
  exact h.trans (TransitionSheaf.holomorphicTransitionCech_sheaf_class E M u)

theorem holomorphicLogTransitionCech_exponential (u : Connecting.holomorphicUnitCohomology E M) :
    Abelian.CechClasses.abelianCechCoefficient (X := TopCat.of M) (Singular.holomorphicLogCover E M u)
      (Sheaves.holomorphicExponentialSheafMap E M).hom 1
      (CechForget.holomorphicCechOfLog E M (Singular.holomorphicLogCover E M u) (Singular.holomorphicLogCech E M u)
        (ChernSheaf.holomorphicLogCech_holomorphic E M u)) = holomorphicLogTransitionCech E M u := by
  funext a
  apply Units.ext
  apply ContMDiffMap.ext
  intro x
  exact Singular.exp_holomorphicLogCech E M u a x

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LogTransition
