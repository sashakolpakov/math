import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SupportedCycleRelativeClass
import OAI.AlgebraicGeometry.ComplexMultiplication.RelativeClassOpenRestriction

/-! # Supported Cycle Smooth Section -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SupportedCycleSmoothSection

noncomputable section

/-! # The genuine whole-cycle class has the original normalized smooth-support section -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint _root_.TopologicalSpace Opposite
open OAI.AlgebraicTopology.Singular

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (p : ℕ) (x : CycleClassMap.OriginalCycleComponent X p)

theorem originalSupportedCycleRelativeClass_smoothSection :
    (AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))
      (Cycle.Support.cycleComponentSupport X x.val) (2 * p)).app
      (op (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x.val))
      (AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ (2 * p)
        (AlgebraicTopology.LocalHomology.NormalProjectionCoclass.Singular.neighborhoodSupportInclusionPairMap
          (Set.subset_univ (ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x.val : Set (ComplexPoint.Basic.ComplexSchemePoint X)))
          (Cycle.Support.cycleComponentSupport X x.val)) (SupportedCycleRelativeClass.originalSupportedCycleRelativeClass X p x)) =
    ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportCoclassSection X x.val x.property := by
  let f := ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap X x.val
  let hf := ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x.val
  let S := Cycle.Support.cycleComponentSupport X x.val
  let B := Set.range (ComplexPoint.Basic.Point.map (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusClosedLiftOver X x.val))
  let hB := ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap_support X x.val
  let U := ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportAmbientOpen X x.val
  let hU := ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x.val
  have ha := RelativeClassOpenRestriction.relativeClassOnOpen_restriction f hf S B hB (2 * p) U hU
    (SupportedCycleRelativeClass.originalSupportedCycleRelativeClass X p x)
  have hl : AlgebraicTopology.Singular.Cohomology.relativeCohomologyMap ℚ (2 * p)
      (RelativeNeighborhoodPullback.neighborhoodSupportPairMap ⟨f, f.hom.continuous⟩ B S hB
        Set.univ Set.univ (fun _ _ => Set.mem_univ _))
      (SupportedCycleRelativeClass.originalSupportedCycleRelativeClass X p x) = RegularThomRelative.originalRegularThomRelativeClass X p x := by
    simpa only [f, S, B, hB, ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothClosedLiftAmbientMap] using!
      SupportedCycleRelativeClass.originalSupportedCycleRelativeClass_regularPullback X p x
  rw [hl] at ha
  have hu := SectionOnOpenUnit.relativeSectionOnOpen_unit f hf S B hB (2 * p) U hU
    (RegularThomRelative.originalRegularThomRelativeClass X p x)
  have hs : AlgebraicTopology.Support.RelativeCohomologyOpenTransport.Singular.supportRelativeCohomologySectionOnOpen f hf S B hB (2 * p) U hU
      ((AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint (Cycle.ComponentSmoothClosedLift.cycleComponentSmoothLocusAmbientOpenOver X x.val))) B
        (2 * p)).app (op ⊤) (RegularThomRelative.originalRegularThomRelativeClass X p x)) =
    ComplexPoint.Basic.ComplexSchemePoint.cycleComponentSmoothSupportCoclassSection X x.val x.property := by
    rw [RegularThomSection.originalRegularThomRelativeClass_section]
    rfl
  exact (congrArg ((AlgebraicTopology.Support.RelativeCohomologySheaf.Singular.supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) S
    (2 * p)).app (op U)) ha).symm.trans (hu.symm.trans hs)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Reference.SupportedCycleSmoothSection
