import OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.FrameChern
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LogarithmicRestriction

/-! # Frame Naturality -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.FrameNaturality

noncomputable section

/-! Naturality of the original Chern class for actual regular frame atlases whose evaluated transitions pull back. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.LogarithmicRestriction.Constructions.CechPullback
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem firstChernClassQ_naturality_of_regularFrames
    {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} {L : Line.Bundles.AlgebraicLineBundle X} {M : Line.Bundles.AlgebraicLineBundle Y}
    {ι : Type} (A : FrameAnalyticTransitions.RegularSectionFrameAtlas L ι) (B : FrameAnalyticTransitions.RegularSectionFrameAtlas M ι)
    (f : Y.toOver ⟶ X.toOver)
    (hdom : ∀ i p, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p ∈ A.analyticDomain i → p ∈ B.analyticDomain i)
    (htrans : ∀ i j p (hi : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p ∈ A.analyticDomain i)
      (hj : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p ∈ A.analyticDomain j),
      B.pointTransition i j p (hdom i p hi) (hdom j p hj) =
        A.pointTransition i j (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) hi hj) :
    First.firstChernClassQ Y M = AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ)
      (TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f)) 2 (First.firstChernClassQ X L) := by
  let g := TopCat.ofHom (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.mapContinuous f)
  let U := HodgeConjecture.DegreeTwo.CechPullbackF.Constructions.CechPullback.pulledCover g A.logCover
  have hU := HodgeConjecture.DegreeTwo.CechPullbackF.Constructions.CechPullback.pulledCover_covers g A.logCover A.logCover_covers
  let l := HodgeConjecture.DegreeTwo.LogarithmicRestriction.Constructions.CechPullback.logarithmPullback g A.logCover A.logCech
  have hl := HodgeConjecture.DegreeTwo.LogarithmicRestriction.Constructions.CechPullback.exponentialCocycle_pullback g A.logCover A.logCech A.logCech_cocycle
  have hsub : ∀ a : A.LogIndex, U a ≤ B.analyticDomain a.2.val := by
    intro a p hp
    exact hdom a.2.val p (A.logCover_subset a hp)
  have hc : LogCech.RationalCech.logarithmicSingularClass (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y.toOver)) U hU l hl =
      First.firstChernClassQ Y M := by
    apply B.firstChernClassQ_eq_on_cover U hU (fun a => a.2.val) hsub l hl
    intro a p
    exact (A.exp_logCech a (HodgeConjecture.DegreeTwo.CechPullbackF.Constructions.CechPullback.intersectionMap g A.logCover a p)).trans
      (htrans (a 0).2.val (a 1).2.val p.val
        (A.logCover_subset (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
        (A.logCover_subset (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))).symm
  exact hc.symm.trans ((HodgeConjecture.DegreeTwo.LogarithmicRestriction.Constructions.CechPullback.logarithmicSingularClass_pullback g A.logCover A.logCover_covers
    A.logCech A.logCech_cocycle).trans
    (congrArg (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℚ ℚ) g 2) A.logCech_firstChernClass))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.FrameNaturality
