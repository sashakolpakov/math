import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.IntrinsicLogCochains
import OAI.AlgebraicGeometry.DivisorClass.Chern.Cech.ConnectingLogLift
import OAI.AlgebraicGeometry.DivisorClass.Chern.SecondCechResolutionRefinement

/-! # Resolution Lifts -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ResolutionLifts

noncomputable section

/-! The original logarithms and local unit lifts form the actual two-step resolution descent. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.TopCat.Sheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type) [TopologicalSpace M] [ChartedSpace E M] [CompactSpace M] [NormalSpace M]
  (u : Connecting.holomorphicUnitCohomology E M) (R : InjectiveResolution (IntegralConstantSheaf.integralConstantSheaf (TopCat.of M)))

def holomorphicLogResolutionLift :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex (Singular.holomorphicLogCover E M u) R.cocomplex).X 0).X 1 :=
  Cech.ConnectingLogLift.nativeConnectingLogLift (X := TopCat.of M) (Singular.holomorphicLogCover E M u) (ShortExact.holomorphicExponentialSequence_shortExact E M)
    R (IntrinsicLogCochains.holomorphicNativeLogCochain E M u)

def holomorphicSecondResolutionLift :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex (Singular.holomorphicLogCover E M u) R.cocomplex).X 1).X 0 :=
  (CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).oneNativeResolutionRefinement
    (Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence_shortExact (Sheaves.holomorphicUnitsSheaf E M)) R
    (ConnectingResolutionCocycle.connectingResolutionQuotient (ShortExact.holomorphicExponentialSequence_shortExact E M) R)
    (Singular.holomorphicLogCover E M u) (fun i => i.2.val) (Singular.holomorphicLogCover_subset E M u)

theorem holomorphicLogResolutionLift_delta :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex (Singular.holomorphicLogCover E M u) R.cocomplex).X 0).d 1 2
      (holomorphicLogResolutionLift E M u R) =
      ((CategoryTheory.cechComplexFunctor (Singular.holomorphicLogCover E M u)).map (R.ι.f 0).hom).f 2
        (IntrinsicLogCochains.holomorphicNativeIntegerDefect E M u) :=
  Cech.ConnectingLogLift.nativeConnectingLogLift_delta (X := TopCat.of M) (Singular.holomorphicLogCover E M u)
    (ShortExact.holomorphicExponentialSequence_shortExact E M) R (IntrinsicLogCochains.holomorphicNativeLogCochain E M u)
    (IntrinsicLogCochains.holomorphicNativeIntegerDefect E M u) (IntrinsicLogCochains.holomorphicNativeLogCochain_period E M u)

theorem holomorphicLogResolutionLift_d :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex (Singular.holomorphicLogCover E M u) R.cocomplex).d 0 1).f 1
      (holomorphicLogResolutionLift E M u R) =
      ((CategoryTheory.cechComplexFunctor (Singular.holomorphicLogCover E M u)).map
        (ConnectingResolutionCocycle.connectingResolutionQuotient (ShortExact.holomorphicExponentialSequence_shortExact E M) R).hom).f 1
        (IntrinsicLogCochains.holomorphicNativeUnitTransition E M u) :=
  Cech.ConnectingLogLift.nativeConnectingLogLift_d (X := TopCat.of M) (Singular.holomorphicLogCover E M u)
    (ShortExact.holomorphicExponentialSequence_shortExact E M) R (IntrinsicLogCochains.holomorphicNativeLogCochain E M u)
    (IntrinsicLogCochains.holomorphicNativeUnitTransition E M u) (IntrinsicLogCochains.holomorphicNativeLogCochain_exponential E M u)

theorem holomorphicSecondResolutionLift_delta :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex (Singular.holomorphicLogCover E M u) R.cocomplex).X 1).d 0 1
      (holomorphicSecondResolutionLift E M u R) =
      ((CategoryTheory.cechComplexFunctor (Singular.holomorphicLogCover E M u)).map
        (ConnectingResolutionCocycle.connectingResolutionQuotient (ShortExact.holomorphicExponentialSequence_shortExact E M) R).hom).f 1
        (IntrinsicLogCochains.holomorphicNativeUnitTransition E M u) :=
  (CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).oneNativeResolutionRefinement_delta
    (Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence_shortExact (Sheaves.holomorphicUnitsSheaf E M)) R
    (ConnectingResolutionCocycle.connectingResolutionQuotient (ShortExact.holomorphicExponentialSequence_shortExact E M) R)
    (Singular.holomorphicLogCover E M u) (fun i => i.2.val) (Singular.holomorphicLogCover_subset E M u)

theorem holomorphicSecondResolutionLift_d :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex (Singular.holomorphicLogCover E M u) R.cocomplex).d 1 2).f 0
      (holomorphicSecondResolutionLift E M u R) =
      FlasqueCechD.abelianCechHorizontalAugmentation (Singular.holomorphicLogCover E M u) R.cocomplex 2
        ((GammaSectionsComparison.abelianGammaSectionsIso R.cocomplex).inv.f 2
          (Sheaf.BoundaryDegreeTwo.sheafSecondConnectingSection (ShortExact.holomorphicExponentialSequence_shortExact E M) R
            (CohomologyTransitions.holomorphicCohomologyRepresentative E M u))) :=
  (CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).oneNativeResolutionRefinement_d
    (Sheaf.CohomologyLifts.sheafInjectiveCokernelSequence_shortExact (Sheaves.holomorphicUnitsSheaf E M)) R
    (ConnectingResolutionCocycle.connectingResolutionQuotient (ShortExact.holomorphicExponentialSequence_shortExact E M) R)
    (ConnectingResolutionCocycle.connectingResolutionQuotient_closed (ShortExact.holomorphicExponentialSequence_shortExact E M) R)
    (Singular.holomorphicLogCover E M u) (fun i => i.2.val) (Singular.holomorphicLogCover_subset E M u)

theorem holomorphicResolutionLifts_middle :
    ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex (Singular.holomorphicLogCover E M u) R.cocomplex).d 0 1).f 1
      (holomorphicLogResolutionLift E M u R) =
      ((SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechBicomplex (Singular.holomorphicLogCover E M u) R.cocomplex).X 1).d 0 1
        (holomorphicSecondResolutionLift E M u R) :=
  (holomorphicLogResolutionLift_d E M u R).trans (holomorphicSecondResolutionLift_delta E M u R).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ResolutionLifts
